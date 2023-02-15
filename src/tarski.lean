import model_theory.basic
import model_theory.syntax
/-
TODO : notations
-/
open_locale first_order
open fin

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
  tarski_language.formula α :=
    first_order.language.relations.bounded_formula
      tarski_relations.point_between
      ![
        first_order.language.term.relabel sum.inl t1,
        first_order.language.term.relabel sum.inl t2,
        first_order.language.term.relabel sum.inl t3
       ]

definition line_cong' {α} {n : ℕ } 
  (t1 t2 t3 t4 : tarski_language.term α) :
  tarski_language.formula α :=
    first_order.language.relations.bounded_formula
      tarski_relations.line_cong
      ![
        first_order.language.term.relabel sum.inl t1,
        first_order.language.term.relabel sum.inl t2,
        first_order.language.term.relabel sum.inl t3,
        first_order.language.term.relabel sum.inl t4
       ]

/-
definition line_cong' {α} {n : ℕ } 
  (t1 t2 t3 t4 : tarski_language.term α) :
  tarski_language.formula α :=
    first_order.language.relations.formula
      tarski_relations.line_cong
      ![t1,t2,t3,t4]
-/