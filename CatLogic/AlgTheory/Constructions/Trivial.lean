import «CatLogic».AlgTheory.Model

open CategoryTheory Limits

namespace AlgTheory.Trivial

def Theory : AlgTheory where
  sig := {
    Op := Empty
    Arity := Empty.rec
    arity_fintype := Empty.rec 
  }
  ax := {
    I := Empty
    Lhs := Empty.rec
    Rhs := Empty.rec
  }

variable {C : Type*} [Category C] [HasFiniteProducts C]

def toCat (C : Type*) [Category C] [HasFiniteProducts C]
: Model Theory C ⥤ C where
  obj := Model.obj
  map := Model.Hom.h

@[simp]
theorem toCat_obj : (toCat C).obj M = M.I.I := rfl
@[simp]
theorem toCat_map : (toCat C).map h = h.h := rfl 

def ofCat (C : Type*) [Category C] [HasFiniteProducts C]
: C ⥤ Model Theory C where
  obj := fun X => {
    I := {
      I := X
      Op := Empty.rec 
    }
    sat_ax := Empty.rec 
  }
  map := fun h => {
    h
    comm := Empty.rec 
  }

@[simp]
theorem ofCat_obj_obj : ((ofCat C).obj X).I.I = X := rfl
@[simp]
theorem ofCat_obj_op : ((ofCat C).obj X).I.Op = Empty.rec := rfl
@[simp]
theorem ofCat_map_h : ((ofCat C).map f).h = f := rfl 

-- lmao i forgot about CategoryTheory.Equivalence.mk for wayyyy too long
theorem equivalence (C : Type*) [Category C] [HasFiniteProducts C]
: Model Theory C ≌ C := CategoryTheory.Equivalence.mk 
  (toCat C)
  (ofCat C)
  (eqToIso (by
    apply Functor.hext
    · intro M
      rw [Functor.id_obj, Functor.comp_obj]
      ext
      · simp
      · simp
        ext ⟨⟩ 
    · intro M N h
      simp [ofCat]
      convert heq_of_eq h.eta.symm))
  (eqToIso (by
    apply Functor.hext
    · intro X
      rw [Functor.comp_obj, Functor.id_obj, toCat_obj, ofCat_obj_obj]
    · intro X Y f
      rw [Functor.comp_map, Functor.id_map, toCat_map, ofCat_map_h]))
--  functor_unitIso_comp := fun M => by simp

end AlgTheory.Trivial
