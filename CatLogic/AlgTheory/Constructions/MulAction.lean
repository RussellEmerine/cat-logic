import «CatLogic».AlgTheory.Model 
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Types

open CategoryTheory Limits

namespace AlgTheory.MulAction

universe u 

def Theory (G : Type*) [Group G] : AlgTheory where
  sig := {
    Op := G
    Arity := fun _ => Unit
    arity_fintype := fun _ => inferInstance 
  }
  ax := {
    I := Option (G × G)
    Lhs := fun
    | none => Sig.Term.Op 1 fun () => Sig.Term.Var "b"
    | some (x, y) => Sig.Term.Op (x * y) fun () => Sig.Term.Var "b"
    Rhs := fun
    | none => Sig.Term.Var "b"
    | some (x, y) => Sig.Term.Op x fun () => Sig.Term.Op y fun () => Sig.Term.Var "b"
  }

-- todo: prove equivalence to MulAction category 

end AlgTheory.MulAction
