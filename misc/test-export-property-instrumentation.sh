#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
model="$repo_dir/examples/regression/trace/export-property-instrumentation.spthy"
restriction_model="$repo_dir/examples/regression/trace/export-restriction-disjunction.spthy"
knowledge_model="$repo_dir/examples/regression/trace/export-knowledge-fragment.spthy"
tamarin=${TAMARIN:-tamarin-prover}
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/tamarin-export-properties.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

export_model_lemma() {
  input=$1
  lemma=$2
  output=$3
  "$tamarin" -d=0 -m=proverif "--lemma=$lemma" "-o=$output" "$input" >/dev/null
}

export_lemma() {
  export_model_lemma "$model" "$1" "$2"
}

require_pattern() {
  pattern=$1
  output=$2
  if ! grep -Eq "$pattern" "$output"; then
    echo "missing pattern in $output: $pattern" >&2
    exit 1
  fi
}

completion="$tmp_dir/completion.pv"
export_lemma completion_required "$completion"
require_pattern '^event eRuleCompleted\(bitstring\)\.$' "$completion"
require_pattern 'event\(eRuleCompleted\( rid[^)]*\)\)' "$completion"
require_pattern 'event eRuleCompleted\(rid_rEmitTogether\)' "$completion"

tautology="$tmp_dir/tautology.pv"
export_lemma completion_not_required_for_same_fact "$tautology"
if grep -q 'RuleCompleted' "$tautology"; then
  echo "same-fact correspondence unexpectedly requested completion" >&2
  exit 1
fi

temporal="$tmp_dir/temporal.pv"
export_lemma temporal_equality_uses_rule_ids "$temporal"
require_pattern '^event eFirst\(bitstring, bitstring\)\.$' "$temporal"
require_pattern '^event eSecond\(bitstring, bitstring\)\.$' "$temporal"
require_pattern '\(rid_[[:alnum:]_]+ = rid_[[:alnum:]_]+\)' "$temporal"

restriction="$tmp_dir/restriction.pv"
"$tamarin" -d=0 -m=proverif --lemma=no_link_chain "-o=$restriction" "$restriction_model" >/dev/null
if [ "$(grep -c '==> (false)' "$restriction")" -ne 2 ]; then
  echo "forbidden disjunction did not produce two false-conclusion restrictions" >&2
  exit 1
fi
require_pattern 'event\(eLink\( x, y \)\).*event\(eLink\( y, z \)\)' "$restriction"
require_pattern 'event\(eLink\( x, y \)\).*event\(eLink\( z, x \)\)' "$restriction"
if grep -q 'Restriction has negated event' "$restriction"; then
  echo "forbidden disjunction retained a negated-event restriction" >&2
  exit 1
fi

knowledge_supported="$tmp_dir/knowledge-supported.pv"
export_model_lemma "$knowledge_model" supported_k "$knowledge_supported"
if grep -q 'Lemma translation failed' "$knowledge_supported"; then
  echo "supported T-UKF formula was rejected" >&2
  exit 1
fi
require_pattern 'attacker\( x \)@j' "$knowledge_supported"
require_pattern 'supported_positive_k_restriction' "$knowledge_supported"
require_pattern 'supported_positive_k_axiom \[reuse/source lemma translated as axiom\]' "$knowledge_supported"
require_pattern 'rejected_negative_k_restriction' "$knowledge_supported"
require_pattern 'Restriction translation failed: NNF\(phi\) contains a negative K atom' "$knowledge_supported"
require_pattern 'rejected_ku_restriction' "$knowledge_supported"
require_pattern 'Restriction translation failed: formula contains KU fact' "$knowledge_supported"
require_pattern 'rejected_negative_k_axiom \[reuse/source lemma not translated as axiom\]' "$knowledge_supported"
require_pattern 'Axiom translation failed: NNF\(phi\) contains a negative K atom' "$knowledge_supported"
require_pattern 'rejected_ku_axiom \[reuse/source lemma not translated as axiom\]' "$knowledge_supported"
require_pattern 'Axiom translation failed: formula contains KU fact' "$knowledge_supported"

knowledge_ku="$tmp_dir/knowledge-ku.pv"
export_model_lemma "$knowledge_model" rejected_ku "$knowledge_ku"
require_pattern 'Lemma translation failed: formula contains KU fact' "$knowledge_ku"

knowledge_exists="$tmp_dir/knowledge-exists.pv"
export_model_lemma "$knowledge_model" rejected_exists_k "$knowledge_exists"
require_pattern 'Lemma translation failed: exists-trace formula contains K fact' "$knowledge_exists"

knowledge_negative="$tmp_dir/knowledge-negative.pv"
export_model_lemma "$knowledge_model" rejected_negative_k "$knowledge_negative"
require_pattern 'Lemma translation failed: formula is outside T-UKF: NNF\(not\(phi\)\) contains a negative K atom' "$knowledge_negative"

if command -v proverif >/dev/null 2>&1; then
  proverif -parse-only "$completion" >/dev/null
  proverif -parse-only "$tautology" >/dev/null
  proverif -parse-only "$temporal" >/dev/null
  proverif -parse-only "$restriction" >/dev/null
  proverif -parse-only "$knowledge_supported" >/dev/null
fi

echo "export property instrumentation regression passed"
