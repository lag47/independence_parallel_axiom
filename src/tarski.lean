import model_theory.basic
import model_theory.syntax
import model_theory.language_map

/-
TODO : notations
-/
open_locale first_order
open fin
namespace first_order
namespace language
namespace term
namespace relations
namespace sum


inductive tarski_relations : ℕ → Type 0
  | point_between : tarski_relations 3
  | line_cong : tarski_relations 4

inductive tarski_functions : ℕ -> Type 0

definition tarski_language : first_order.language :=
  {
    functions := tarski_functions,
    relations := tarski_relations
  }

definition point_between' {α} {n : ℕ } 
  (t1 t2 t3 : tarski_language.term α) :
  tarski_language.bounded_formula α n :=
    relations.bounded_formula
      tarski_relations.point_between
      ![
        relabel sum.inl t1,
        relabel sum.inl t2,
        relabel sum.inl t3
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



definition tarski_axiom1_open {α} : tarski_language.bounded_formula α (fin 2) :=
  line_cong' (var fin0) (var fin1) (var fin1) (var fin0)

definition tarski_axiom1 : tarski_language.formula (fin 0) :=
  bounded_formula.alls tarski_axiom1_open

/-
definition tarski_axiom1 {α} : tarski_language.formula α :=
 first_order.language.bounded_formula.alls
  (line_cong' _ _ _ _)
-/
/-
definition line_cong' {α} {n : ℕ } 
  (t1 t2 t3 t4 : tarski_language.term α) :
  tarski_language.formula α :=
    first_order.language.relations.formula
      tarski_relations.line_cong
      ![t1,t2,t3,t4]
-/