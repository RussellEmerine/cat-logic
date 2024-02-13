import «CatLogic».AlgTheory.Model
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Category.Pointed

open CategoryTheory Limits

universe u

namespace AlgTheory.Pointed

def Theory : AlgTheory where
  sig := {
    Op := Unit
    Arity := fun () => Empty
    arity_fintype := fun () => inferInstance 
  }
  ax := {
    I := Empty
    Lhs := Empty.rec
    Rhs := Empty.rec 
  }

open Types 

theorem equiv
: Model Theory (Type u) ≌ Pointed.{u} := CategoryTheory.Equivalence.mk 
  { obj := fun M => {
      X := M.I.I
      point := M.I.Op () ((powIso _ _).inv Empty.rec)
    }
    map := fun {M N} f => {
      toFun := f.h
      map_point := by
        dsimp
        have := congrFun (f.comm ()) ((powIso _ _).inv Empty.rec)
        simp at this
        rw [this]
        apply congrArg (Sig.Interp.Op N.I ())
        ext ⟨⟨⟩⟩ 
    }
  }
  { obj := fun X => {
      I := {
        I := X.X
        Op := fun () _ => X.point 
      }
      sat_ax := Empty.rec 
    }
    map := fun f => {
      h := f.toFun 
      comm := fun () => by
        ext 
        exact f.map_point
    }
  }
  (eqToIso (by
    apply Functor.hext
    · intro M
      ext
      · simp
      · simp
        ext ⟨⟩ 
        simp
        apply congrArg (Sig.Interp.Op M.I ())
        apply limit_ext
        intro ⟨x⟩
        cases x
    · intro M N f
      rw [Functor.id_map, Functor.comp_map]
      dsimp
      rw [Model.hom_heq_iff]
      · ext
        · rfl
        simp
        ext ⟨⟩ 
        simp
        apply congrArg (Sig.Interp.Op M.I ())
        apply limit_ext
        intro ⟨x⟩
        cases x
      -- all_goals doesn't work :(
      · ext
        · rfl
        simp
        ext ⟨⟩ 
        simp
        apply congrArg (Sig.Interp.Op N.I ())
        apply limit_ext
        intro ⟨x⟩
        cases x))
  (eqToIso (by
    apply Functor.hext
    · intro X
      simp
    intro X Y f
    simp
    rfl))

end AlgTheory.Pointed
