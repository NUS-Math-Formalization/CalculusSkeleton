import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

macro "differentiability" : tactic => `(tactic|(
  repeat' (first |
    exact differentiableAt_id' |
    exact differentiableAt_const _ |
    exact Real.differentiableAt_sin |
    exact Real.differentiableAt_cos |
    exact Real.differentiableAt_tan |
    exact Real.differentiableAt_exp |
    exact differentiableAt_pow _ |
    apply DifferentiableAt.const_mul |
    apply DifferentiableAt.add |
    apply DifferentiableAt.sub |
    apply DifferentiableAt.mul |
    apply DifferentiableAt.div |
    apply DifferentiableAt.pow
  )))
