import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

macro "differentiability" : tactic => `(tactic|(
  repeat' (first |
    -- rw [← Function.comp_def] |
    -- apply DifferentiableAt.comp |
    apply DifferentiableAt.add |
    apply DifferentiableAt.sub |
    apply DifferentiableAt.mul |
    apply DifferentiableAt.div |
    apply DifferentiableAt.pow |
    apply DifferentiableAt.inv |
    apply DifferentiableAt.const_mul |
    apply differentiableAt_const _ |
    apply differentiableAt_id' |
    apply Real.differentiableAt_sin |
    apply Real.differentiableAt_cos |
    apply Real.differentiableAt_tan |
    apply Real.differentiableAt_exp |
    apply Real.differentiableAt_log |
    apply Real.differentiableAt_pow _ |

    assumption
  )))

macro "derivit" : tactic => `(tactic|(
  repeat' (first |
    rw [deriv_id''] |
    rw [deriv_add] |
    rw [deriv_pow''] |
    rw [deriv_const] |
    rw [deriv_inv] |
    rw [deriv_pow] |
    rw [deriv_div] |
    rw [deriv_const_mul] |
    rw [deriv_sub_const] |
    rw [Real.deriv_const'] |
    rw [Real.deriv_sin] |
    rw [Real.deriv_cos] |
    rw [← Function.comp_def] |
    rw [deriv.comp] |


    simp_all
  )))
