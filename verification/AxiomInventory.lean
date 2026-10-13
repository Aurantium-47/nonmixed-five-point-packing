import W01

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    if let .axiomInfo info := ci then
      logInfo m!"AMBIENT_AXIOM {name} : {info.type}"

#print axioms W01.packing_upper_bound
#print axioms W01.exists_optimal_packing
#print axioms W01.packingDensity_formula
#print axioms W01.packingDensity_formula_euclidean
