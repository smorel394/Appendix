/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Homology.HomotopyCategory
import Appendix.Mathlib.Algebra.Homology.Additive

/-!
# The homotopy category

Addendum to the mathlib file.
-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

namespace CategoryTheory

variable {V} {W : Type*} [Category W] [Preadditive W]

def Functor.mapHomotopyCategoryCompIso {W' : Type*} [Category W'] [Preadditive W']
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι) :
    H.mapHomotopyCategory c ≅ F.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c :=
  Quotient.natIsoLift _ (isoWhiskerRight (Functor.mapHomologicalComplexCompIso e c)
    (HomotopyCategory.quotient W' c))

section

variable {c}
variable (F : V ⥤ W) [F.Additive] [F.Full] [F.Faithful]

def Functor.preimageHomotopy {K L : HomologicalComplex V c} (f₁ f₂ : K ⟶ L)
    (H : Homotopy ((F.mapHomologicalComplex c).map f₁) ((F.mapHomologicalComplex c).map f₂)) :
    Homotopy f₁ f₂ :=
      { hom := fun i j => F.preimage (H.hom i j)
        zero := fun i j hij => F.map_injective (by
          simp only [map_preimage, Functor.map_zero]
          rw [H.zero i j hij])
        comm := fun i => F.map_injective (by
          refine (H.comm i).trans ?_
          rw [F.map_add, F.map_add]
          congr 2
          · dsimp [fromNext]
            simp
          · dsimp [toPrev]
            simp) }

instance [F.Full] [F.Faithful] : (F.mapHomotopyCategory (ComplexShape.up ℤ)).Full where
  map_surjective := by
    intro X Y f
    obtain ⟨f₁, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    obtain ⟨f₂, rfl⟩ := (F.mapHomologicalComplex _).map_surjective f₁
    use (HomotopyCategory.quotient _ _).map f₂
    simp
instance : (F.mapHomotopyCategory c).Faithful where
  map_injective := by
    rintro ⟨K⟩ ⟨L⟩ f₁ f₂ h
    obtain ⟨f₁, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f₂
    exact HomotopyCategory.eq_of_homotopy _ _
      (F.preimageHomotopy _ _ (HomotopyCategory.homotopyOfEq _ _ h))

end

end CategoryTheory
