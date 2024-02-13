import Mathlib.Data.Fintype.Basic

/-
Signature of an algebraic theory.

An earlier version had Op as a parameter rather than a structure field.
This makes some things harder to prove, but has fewer types floating around.
-/
structure Sig where
  Op : Type*
  Arity : Op → Type*
  -- used to use Finite instead of Fintype, but this is also manageable 
  arity_fintype : (op : Op) → Fintype (Arity op)

namespace Sig

variable {sig : Sig}

instance : ∀ op, Fintype (sig.Arity op) := sig.arity_fintype 

theorem ext_iff (sig₁ sig₂ : Sig)
: sig₁ = sig₂ ↔ sig₁.Op = sig₂.Op ∧ HEq sig₁.Arity sig₂.Arity := by
  rcases sig₁ with ⟨Op₁, Arity₁, _⟩
  rcases sig₂ with ⟨Op₂, Arity₂, _⟩
  simp
  intro h₁ h₂ 
  subst h₁ h₂
  rw [heq_iff_eq]
  apply Subsingleton.elim

@[ext]
theorem ext (sig₁ sig₂ : Sig) (h₁ : sig₁.Op = sig₂.Op) (h₂ : HEq sig₁.Arity sig₂.Arity)
: sig₁ = sig₂ :=
  (ext_iff sig₁ sig₂).mpr ⟨h₁, h₂⟩ 

-- A variable in a term. Any infinite type will do, but strings are nice visually.
abbrev Variable := String 

/-
A term for a signature.

An earlier version had the context as a parameter,
but it turns out that's not what the book says.
-/
inductive Term (sig : Sig) where
| Var : Variable → sig.Term
| Op : (op : sig.Op) → (sig.Arity op → sig.Term) → sig.Term

namespace Term

def vars : sig.Term → Finset Variable
| Var x => {x}
| Op _ f => Finset.univ.biUnion fun i => (f i).vars

theorem vars_var_mem (x : Variable)
: x ∈ (Var x : sig.Term).vars :=
  Finset.mem_singleton_self x

theorem vars_op_subset (op : sig.Op) (f : sig.Arity op → sig.Term) (i : sig.Arity op)
: (f i).vars ⊆ (Op op f).vars :=
  Finset.subset_biUnion_of_mem (fun i => vars (f i)) (Finset.mem_univ i)

end Term

-- Axioms in a signature, could've been written as pairs but indexed form is more useful
structure Ax (sig : Sig) where 
  I : Type*
  Lhs : I → sig.Term
  Rhs : I → sig.Term

namespace Ax

theorem ext_iff (ax₁ ax₂ : sig.Ax)
: ax₁ = ax₂
  ↔ ax₁.I = ax₂.I
    ∧ HEq ax₁.Lhs ax₂.Lhs
    ∧ HEq ax₁.Rhs ax₂.Rhs := by
  rcases ax₁ with ⟨I₁, Lhs₁, Rhs₁⟩
  rcases ax₂ with ⟨I₂, Lhs₂, Rhs₂⟩
  simp

@[ext]
theorem ext (ax₁ ax₂ : sig.Ax)
  (h₁ : ax₁.I = ax₂.I)
  (h₂ : HEq ax₁.Lhs ax₂.Lhs)
  (h₃ : HEq ax₁.Rhs ax₂.Rhs)
: ax₁ = ax₂ :=
  (ext_iff ax₁ ax₂).mpr ⟨h₁, h₂, h₃⟩ 

end Ax

end Sig

structure AlgTheory where
  sig : Sig
  ax : sig.Ax

namespace AlgTheory

theorem ext_iff (alg₁ alg₂ : AlgTheory)
: alg₁ = alg₂ ↔ alg₁.sig = alg₂.sig ∧ HEq alg₁.ax alg₂.ax := by
  rcases alg₁ with ⟨sig₁, ax₁⟩
  rcases alg₂ with ⟨sig₂, ax₂⟩
  simp

@[ext]
theorem ext (alg₁ alg₂ : AlgTheory)
  (h₁ : alg₁.sig = alg₂.sig)
  (h₂ : HEq alg₁.ax alg₂.ax)
: alg₁ = alg₂ :=
  (ext_iff alg₁ alg₂).mpr ⟨h₁, h₂⟩ 

end AlgTheory
