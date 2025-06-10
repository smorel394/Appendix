/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Triangulated.Basic

/-!
# Triangles

Addendum to the mathlib file.
-/


noncomputable section

open CategoryTheory Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

/-
We work in a category `C` equipped with a shift.
-/
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

section

open ZeroObject

variable {T₁ T₂ T₃ : Triangle C}

section Preadditive

variable [Preadditive C]

attribute [local simp] Preadditive.comp_zsmul Preadditive.zsmul_comp
  Preadditive.comp_nsmul Preadditive.nsmul_comp Functor.map_zsmul Functor.map_nsmul

variable (T₁ T₂)
variable [∀ (n : ℤ), (shiftFunctor C n).Additive]

section

instance : Zero (T₁ ⟶ T₂) where
  zero :=
    { hom₁ := 0
      hom₂ := 0
      hom₃ := 0 }

@[simp] lemma Triangle.zero_hom₁ : (0 : T₁ ⟶ T₂).hom₁ = 0 := rfl
@[simp] lemma Triangle.zero_hom₂ : (0 : T₁ ⟶ T₂).hom₂ = 0 := rfl
@[simp] lemma Triangle.zero_hom₃ : (0 : T₁ ⟶ T₂).hom₃ = 0 := rfl

variable {T₁ T₂}

@[simps]
instance : Add (T₁ ⟶ T₂) where
  add f g :=
    { hom₁ := f.hom₁ + g.hom₁
      hom₂ := f.hom₂ + g.hom₂
      hom₃ := f.hom₃ + g.hom₃ }

@[simp] lemma Triangle.add_hom₁ (f g : T₁ ⟶ T₂) : (f + g).hom₁ = f.hom₁ + g.hom₁ := rfl
@[simp] lemma Triangle.add_hom₂ (f g : T₁ ⟶ T₂) : (f + g).hom₂ = f.hom₂ + g.hom₂ := rfl
@[simp] lemma Triangle.add_hom₃ (f g : T₁ ⟶ T₂) : (f + g).hom₃ = f.hom₃ + g.hom₃ := rfl

@[simps]
instance : Neg (T₁ ⟶ T₂) where
  neg f :=
    { hom₁ := -f.hom₁
      hom₂ := -f.hom₂
      hom₃ := -f.hom₃ }

@[simp] lemma Triangle.neg_hom₁ (f : T₁ ⟶ T₂) : (-f).hom₁ = -f.hom₁ := rfl
@[simp] lemma Triangle.neg_hom₂ (f : T₁ ⟶ T₂) : (-f).hom₂ = -f.hom₂ := rfl
@[simp] lemma Triangle.neg_hom₃ (f : T₁ ⟶ T₂) : (-f).hom₃ = -f.hom₃ := rfl

@[simps]
instance : Sub (T₁ ⟶ T₂) where
  sub f g :=
    { hom₁ := f.hom₁ - g.hom₁
      hom₂ := f.hom₂ - g.hom₂
      hom₃ := f.hom₃ - g.hom₃ }

@[simp] lemma Triangle.sub_hom₁ (f g : T₁ ⟶ T₂) : (f - g).hom₁ = f.hom₁ - g.hom₁ := rfl
@[simp] lemma Triangle.sub_hom₂ (f g : T₁ ⟶ T₂) : (f - g).hom₂ = f.hom₂ - g.hom₂ := rfl
@[simp] lemma Triangle.sub_hom₃ (f g : T₁ ⟶ T₂) : (f - g).hom₃ = f.hom₃ - g.hom₃ := rfl

end

section

variable {R : Type*} [Semiring R] [Linear R C]
  [∀ (n : ℤ), Functor.Linear R (shiftFunctor C n)]

@[simps!]
instance  :
    SMul R (T₁ ⟶ T₂) where
  smul n f :=
    { hom₁ := n • f.hom₁
      hom₂ := n • f.hom₂
      hom₃ := n • f.hom₃ }

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] in
@[simp] lemma Triangle.smul_hom₁ (n : R) (f : T₁ ⟶ T₂) : (n • f).hom₁ = n • f.hom₁ := rfl

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] in
@[simp] lemma Triangle.smul_hom₂ (n : R) (f : T₁ ⟶ T₂) : (n • f).hom₂ = n • f.hom₂ := rfl

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] in
@[simp] lemma Triangle.smul_hom₃ (n : R) (f : T₁ ⟶ T₂) : (n • f).hom₃ = n • f.hom₃ := rfl

end

instance instAddCommGroupTriangleHom : AddCommGroup (T₁ ⟶ T₂) where
  zero_add f := by ext <;> apply zero_add
  add_assoc f g h := by ext <;> apply add_assoc
  add_zero f := by ext <;> apply add_zero
  add_comm f g := by ext <;> apply add_comm
  neg_add_cancel f := by ext <;> apply neg_add_cancel
  sub_eq_add_neg f g := by ext <;> apply sub_eq_add_neg
  nsmul n f := n • f
  nsmul_zero f := by aesop_cat
  nsmul_succ n f := by ext <;> apply AddMonoid.nsmul_succ
  zsmul n f := n • f
  zsmul_zero' := by aesop_cat
  zsmul_succ' n f := by ext <;> apply SubNegMonoid.zsmul_succ'
  zsmul_neg' n f := by ext <;> apply SubNegMonoid.zsmul_neg'

instance instPreadditiveTriangle : Preadditive (Triangle C) where

end Preadditive

section Linear

variable [Preadditive C] {R : Type*} [Semiring R] [Linear R C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), Functor.Linear R (shiftFunctor C n)]

attribute [local simp] mul_smul add_smul

instance (T₁ T₂ : Triangle C) : Module R (T₁ ⟶ T₂) where
  one_smul := by aesop
  mul_smul := by aesop
  smul_zero := by aesop
  smul_add := by aesop
  add_smul := by aesop
  zero_smul := by aesop

instance : Linear R (Triangle C) where

end Linear

namespace Triangle

@[simps]
def π₁Toπ₂ : (π₁ : Triangle C ⥤ C) ⟶ Triangle.π₂ where
  app T := T.mor₁

@[simps]
def π₂Toπ₃ : (π₂ : Triangle C ⥤ C) ⟶ Triangle.π₃ where
  app T := T.mor₂

@[simps]
def π₃Toπ₁ : (π₃ : Triangle C ⥤ C) ⟶ π₁ ⋙ shiftFunctor C (1 : ℤ) where
  app T := T.mor₃

section

variable {A B : Triangle C} (φ : A ⟶ B) [IsIso φ]

instance : IsIso φ.hom₁ := (inferInstance : IsIso (π₁.map φ))
instance : IsIso φ.hom₂ := (inferInstance : IsIso (π₂.map φ))
instance : IsIso φ.hom₃ := (inferInstance : IsIso (π₃.map φ))

end

variable {J : Type _} [Category J]

@[simps]
def functorMk {obj₁ obj₂ obj₃ : J ⥤ C}
    (mor₁ : obj₁ ⟶ obj₂) (mor₂ : obj₂ ⟶ obj₃) (mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)) :
    J ⥤ Triangle C where
  obj j := mk (mor₁.app j) (mor₂.app j) (mor₃.app j)
  map φ :=
    { hom₁ := obj₁.map φ
      hom₂ := obj₂.map φ
      hom₃ := obj₃.map φ }

@[simps]
def functorHomMk (A B : J ⥤ Triangle C) (hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁)
    (hom₂ : A ⋙ π₂ ⟶ B ⋙ π₂) (hom₃ : A ⋙ π₃ ⟶ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ hom₂ = hom₁ ≫ whiskerLeft B π₁Toπ₂)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ hom₃ = hom₂ ≫ whiskerLeft B π₂Toπ₃)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight hom₁ (shiftFunctor C (1 : ℤ)) =
      hom₃ ≫ whiskerLeft B π₃Toπ₁) : A ⟶ B where
  app j :=
    { hom₁ := hom₁.app j
      hom₂ := hom₂.app j
      hom₃ := hom₃.app j
      comm₁ := NatTrans.congr_app comm₁ j
      comm₂ := NatTrans.congr_app comm₂ j
      comm₃ := NatTrans.congr_app comm₃ j }
  naturality _ _ φ := by
    ext
    · exact hom₁.naturality φ
    · exact hom₂.naturality φ
    · exact hom₃.naturality φ

@[simps!]
def functorHomMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : ℤ)}
    (hom₁ : obj₁ ⟶ obj₁') (hom₂ : obj₂ ⟶ obj₂') (hom₃ : obj₃ ⟶ obj₃')
    (comm₁ : mor₁ ≫ hom₂ = hom₁ ≫ mor₁')
    (comm₂ : mor₂ ≫ hom₃ = hom₂ ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight hom₁ (shiftFunctor C (1 : ℤ)) = hom₃ ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ⟶ functorMk mor₁' mor₂' mor₃' :=
  functorHomMk _ _ hom₁ hom₂ hom₃ comm₁ comm₂ comm₃

@[simps]
def functorIsoMk (A B : J ⥤ Triangle C) (iso₁ : A ⋙ π₁ ≅ B ⋙ π₁)
    (iso₂ : A ⋙ π₂ ≅ B ⋙ π₂) (iso₃ : A ⋙ π₃ ≅ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ iso₂.hom = iso₁.hom ≫ whiskerLeft B π₁Toπ₂)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ iso₃.hom = iso₂.hom ≫ whiskerLeft B π₂Toπ₃)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : ℤ)) =
      iso₃.hom ≫ whiskerLeft B π₃Toπ₁) : A ≅ B where
  hom := functorHomMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := functorHomMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_epi iso₁.hom, ← reassoc_of% comm₁,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by simp only [← cancel_epi iso₂.hom, ← reassoc_of% comm₂,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by
      simp only [← cancel_epi iso₃.hom, ← reassoc_of% comm₃, Iso.hom_inv_id_assoc,
        ← whiskerRight_comp, Iso.hom_inv_id, whiskerRight_id']
      apply comp_id)

@[simps!]
def functorIsoMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : ℤ)}
    (iso₁ : obj₁ ≅ obj₁') (iso₂ : obj₂ ≅ obj₂') (iso₃ : obj₃ ≅ obj₃')
    (comm₁ : mor₁ ≫ iso₂.hom = iso₁.hom ≫ mor₁')
    (comm₂ : mor₂ ≫ iso₃.hom = iso₂.hom ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : ℤ)) = iso₃.hom ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ≅ functorMk mor₁' mor₂' mor₃' :=
  functorIsoMk _ _ iso₁ iso₂ iso₃ comm₁ comm₂ comm₃

end Triangle

end

end CategoryTheory.Pretriangulated

end
