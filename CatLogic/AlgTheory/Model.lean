import «CatLogic».AlgTheory.Basic
import «CatLogic».CatTheory.Pow
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Data.Set.Finite
import Mathlib.Data.List.FinRange

open CategoryTheory Limits

namespace Sig

/-
A context for evaluating a term.
-/
abbrev Ctx := Finset Variable 

namespace Ctx

abbrev I (ctx : Ctx) : Type := ctx 

def covers (ctx : Ctx) {sig : Sig} (term : sig.Term) : Prop :=
  term.vars ⊆ ctx

theorem covers_var_mem (ctx : Ctx) {sig : Sig} (x : Variable) (h : ctx.covers (Term.Var x : sig.Term))
: x ∈ ctx :=
  h (Term.vars_var_mem x)

theorem covers_op (ctx : Ctx) {sig : Sig} (op : sig.Op) (f : sig.Arity op → sig.Term)
  (h : ctx.covers (Term.Op op f)) (i : sig.Arity op)
: ctx.covers (f i) :=
  (Term.vars_op_subset op f i).trans h

theorem union_covers_left (ctx₁ ctx₂ : Ctx) {sig : Sig} (term : sig.Term) (h : ctx₁.covers term)
: (ctx₁ ∪ ctx₂).covers term := by
  apply h.trans
  intro x hx
  simp [Union.union]
  exact Or.inl hx 

theorem union_covers_right (ctx₁ ctx₂ : Ctx) {sig : Sig} (term : sig.Term) (h : ctx₂.covers term)
: (ctx₁ ∪ ctx₂).covers term := by
  apply h.trans
  intro x hx
  simp [Union.union]
  exact Or.inr hx 

noncomputable def ofTerm {sig : Sig} (term : sig.Term) : Ctx :=
  term.vars 

theorem ofTerm_covers {sig : Sig} (term : sig.Term)
: (ofTerm term).covers term := by
  simp [ofTerm, covers]

end Ctx

/-
An interpretation of a signature in category C.
-/
structure Interp (sig : Sig) (C : Type*) [Category C] [HasFiniteProducts C] where
  I : C
  Op : (op : sig.Op) → I ^ᶜ sig.Arity op ⟶ I

namespace Interp

variable {sig : Sig} {C : Type*} [Category C] [HasFiniteProducts C]

theorem ext_iff (I₁ I₂ : sig.Interp C)
: I₁ = I₂ ↔ I₁.I = I₂.I ∧ HEq I₁.Op I₂.Op := by
  rcases I₁ with ⟨I₁, Op₁⟩
  rcases I₂ with ⟨I₂, Op₂⟩
  simp

@[ext]
theorem ext (I₁ I₂ : sig.Interp C)
  (h₁ : I₁.I = I₂.I)
  (h₂ : HEq I₁.Op I₂.Op)
: I₁ = I₂ :=
  (ext_iff I₁ I₂).mpr ⟨h₁, h₂⟩

noncomputable def interp (I : sig.Interp C) (ctx : Ctx) 
: (term : sig.Term) → ctx.covers term → (I.I ^ᶜ ctx.I ⟶ I.I)
| Term.Var x, h => Pow.π ⟨_, ctx.covers_var_mem x h⟩
| Term.Op op f, h => Pow.lift (fun i => I.interp ctx (f i) (ctx.covers_op _ _ h _)) ≫ I.Op op 

def sat_eqn (I : sig.Interp C) (t₁ t₂ : sig.Term) : Prop :=
  ∀ (ctx : Ctx) (h₁ : ctx.covers t₁) (h₂ : ctx.covers t₂),
    I.interp ctx t₁ h₁ = I.interp ctx t₂ h₂ 

def sat_ax (I : sig.Interp C) (ax : sig.Ax) : Prop :=
  ∀ i, I.sat_eqn (ax.Lhs i) (ax.Rhs i)

end Interp

end Sig

structure Model (alg : AlgTheory) (C : Type*) [Category C] [HasFiniteProducts C] where
  I : alg.sig.Interp C
  sat_ax : I.sat_ax alg.ax

namespace Model

variable {alg : AlgTheory} {C : Type*} [Category C] [HasFiniteProducts C]

theorem ext_iff (M₁ M₂ : Model alg C)
: M₁ = M₂ ↔ M₁.I = M₂.I := by
  rcases M₁ with ⟨I₁, _⟩
  rcases M₂ with ⟨I₂, _⟩
  simp

@[ext]
theorem ext (M₁ M₂ : Model alg C) (h : M₁.I = M₂.I)
: M₁ = M₂ :=
  (ext_iff M₁ M₂).mpr h

abbrev obj (M : Model alg C) : C := M.I.I

structure Hom (M N : Model alg C) where
  h : M.obj ⟶ N.obj
  comm : ∀ op, M.I.Op op ≫ h = Pow.map_all _ h ≫ N.I.Op op

namespace Hom

theorem ext_iff {M N : Model alg C} (h₁ h₂ : M.Hom N)
: h₁ = h₂ ↔ h₁.h = h₂.h := by
  rcases h₁ with ⟨h₁, _⟩
  rcases h₂ with ⟨h₂, _⟩
  simp

@[ext]
theorem ext {M N : Model alg C} (h₁ h₂ : M.Hom N) (h : h₁.h = h₂.h)
: h₁ = h₂ :=
  (ext_iff h₁ h₂).mpr h

theorem eta {M N : Model alg C} (h : M.Hom N)
: mk h.h h.comm = h := rfl

def id (M : Model alg C) : M.Hom M where
  h := CategoryStruct.id M.obj 
  comm := fun op => by
    rw [Pow.map_all_id, Category.id_comp]
    exact Category.comp_id (M.I.Op op)

def comp {M N O : Model alg C} (f : M.Hom N) (g : N.Hom O)
: M.Hom O where
  h := f.h ≫ g.h
  comm := fun op => by
    rw [← Category.assoc, f.comm op, Category.assoc, g.comm op, ← Category.assoc, Pow.map_all_comp_map_all]

end Hom

instance : Category (Model alg C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := fun {M N} h => by
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  comp_id := fun {M N} h => by
    apply Hom.ext
    simp [Hom.comp, Hom.id]
  assoc := fun {M N O P} f g h => by
    apply Hom.ext
    simp [Hom.comp]

-- i used this before i realized CategoryTheory.Equivalence.mk exists
@[simp]
def eqToHom_h {M N : Model alg C} (p : M = N)
: (eqToHom p).h = eqToHom (congrArg obj p) := by
  subst p
  rfl

theorem hom_heq_iff {M₁ M₂ N₁ N₂ : Model alg C} (hM : M₁ = M₂) (hN : N₁ = N₂)
  (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
: HEq f g ↔ HEq f.h g.h := by
  subst hM hN
  simp
  rw [Hom.ext_iff]

end Model
  


