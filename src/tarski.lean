import model_theory.basic
import model_theory.syntax
import model_theory.language_map

open_locale first_order
open fin
namespace first_order
namespace language
namespace term



inductive tarski_relations : ℕ → Type 0
  | point_between : tarski_relations 3
  | line_cong : tarski_relations 4

inductive tarski_functions : ℕ -> Type 0

definition tarski_language : first_order.language :=
  {
    functions := tarski_functions,
    relations := tarski_relations
  }


local prefix `'∀s` : 66 := bounded_formula.alls
local prefix `'∀` : 66 := bounded_formula.all
--local notation '&\' n' :=

definition point_between' {α} {n : ℕ } 
  (t1 t2 t3 : tarski_language.term (fin n)) :
  tarski_language.bounded_formula α n :=
    relations.bounded_formula
      tarski_relations.point_between
      ![
        relabel sum.inr t1,
        relabel sum.inr t2,
        relabel sum.inr t3
       ]

definition line_cong' {α} {n : ℕ } 
  (t1 t2 t3 t4 : tarski_language.term (fin n)) :
  tarski_language.bounded_formula α n :=
    relations.bounded_formula
      tarski_relations.line_cong
      ![
        relabel sum.inr t1,
        relabel sum.inr t2,
        relabel sum.inr t3,
        relabel sum.inr t4
       ]

definition fin0 : fin 2 := 0 % 2
definition fin1 : fin 2 := 1 % 2

local prefix `'&` : 75 := (fun (n : nat) , var n)

local notation  w `⬝` : 70 x `≅` : 70  y `⬝` z : 70 :=
  line_cong' w x y z

definition tarski_axiom1 {α}: tarski_language.formula α :=
  ∀' ∀' ((var fin0) ⬝ (var fin1) ≅ (var fin1) ⬝ (var fin0))

end term
end language
end first_order


