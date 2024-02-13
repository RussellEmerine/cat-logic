import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Types

/-
Objects to type powers. In other words, non-dependent products.

Maybe there's a file in Mathlib that does this,
but I have a suspicion there isn't.
-/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {X Y Z : C} {J : Type*} 

abbrev HasPow (X : C) (J : Type*) := HasProduct fun (_ : J) => X

noncomputable section

variable [HasPow X J] [HasPow Y J] [HasPow Z J]

abbrev powObj (X : C) (J : Type*) [HasPow X J] : C := piObj fun (_ : J) => X

infix:60 " ^ᶜ " => powObj

abbrev Pow.π (j : J) : X ^ᶜ J ⟶ X := Pi.π _ j

theorem Pow.hom_ext {A : C} (g₁ g₂ : A ⟶ X ^ᶜ J) (h : ∀ j, g₁ ≫ Pow.π j = g₂ ≫ Pow.π j)
: g₁ = g₂ :=
  Pi.hom_ext g₁ g₂ h

def powIsPow (X : C) (J : Type*) [HasPow X J]
: IsLimit (Fan.mk (X ^ᶜ J) Pow.π) :=
  productIsProduct fun (_ : J) => X

-- maybe (probably) add some eqToHom simp lemmas here

abbrev Pow.lift {P : C} (f : J → (P ⟶ X)) : P ⟶ X ^ᶜ J :=
  Pi.lift f

abbrev Pow.map (p : J → (X ⟶ Y)) : X ^ᶜ J ⟶ Y ^ᶜ J :=
  Pi.map p

@[simp]
theorem Pow.map_id
: Pow.map (fun (_ : J) => 𝟙 X) = 𝟙 (X ^ᶜ J) := 
  Pi.map_id

@[simp]
theorem Pow.map_comp_map (f : J → (X ⟶ Y)) (g : J → (Y ⟶ Z))
: Pow.map f ≫ Pow.map g = Pow.map fun j => f j ≫ g j :=
  Pi.map_comp_map f g 

instance Pow.map_mono (f : J → (X ⟶ Y)) [∀ j, Mono (f j)]
: Mono (Pow.map f) :=
  Pi.map_mono f

abbrev Pow.map_all (J : Type*) [HasPow X J] [HasPow Y J] (f : X ⟶ Y) : X ^ᶜ J ⟶ Y ^ᶜ J :=
  Pow.map fun _ => f

@[simp]
theorem Pow.map_all_id
: Pow.map_all J (𝟙 X) = 𝟙 (X ^ᶜ J) := 
  Pow.map_id

@[simp]
theorem Pow.map_all_comp_map_all (f : X ⟶ Y) (g : Y ⟶ Z)
: Pow.map_all J f ≫ Pow.map_all J g = Pow.map_all J (f ≫ g) :=
  Pow.map_comp_map _ _

instance Pow.map_all_mono (f : X ⟶ Y) [Mono f]
: Mono (Pow.map_all J f) :=
  Pow.map_mono fun _ => f

-- the products file has cones and whisker equivs and other stuff i'll skip for now

def Types.powIso (X : TypeMax.{u, v}) (J : Type u)
: X ^ᶜ J ≅ J → X :=
  Types.productIso fun _ => X 

end 

end CategoryTheory.Limits
