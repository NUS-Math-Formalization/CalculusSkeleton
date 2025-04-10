import Lean
import Mathlib


open Lean PrettyPrinter Delaborator SubExpr

def foo : Nat → Nat := fun x => 42


@[delab app.foo]
def delabfoo2 : Delab := do
  `(2)

@[delab app.foo]
def delabfooFinal : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `foo 1 -- only delab full applications this way
  let fn := mkIdent `fooSpecial
  let arg ← withAppArg delab
  `($fn $arg)

#check foo 42 -- fooSpecial 42 : Nat
#check foo -- 2 : Nat → Nat, still 2 since 3 failed

#check foo -- 2 : Nat → Nat

#check foo -- 1 : Nat → Nat
#check foo 13 -- 1 : Nat, full applications are also pretty printed this way

open Classical
open Filter Set
set_option pp.explicit false

--open Lean Lean.PrettyPrinter.Delaborator

noncomputable def flim (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  if h : ∃ L, Tendsto f (nhds c) (nhds L) then Classical.choose h else 0

syntax "lim " ident "→" term:10 ", " term:60 : term
macro_rules
  | `(lim $x:ident→$c,$f) => `(flim (fun $x => $f) $c)

@[app_unexpander flim]
def flim.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $c) =>
      match f with
     | `(fun $x:ident => $body)=>
        `(lim $x → $c,  $body)
     | _ => throw ()
  | _ => throw ()
