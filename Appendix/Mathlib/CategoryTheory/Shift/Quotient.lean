/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Quotient

/-!
# The shift on a quotient category

Addendum to mathlib file.

-/

universe v v' u u' w

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (r : HomRel C) (A : Type w) [AddMonoid A] [HasShift C A] [HasShift D A]

namespace CategoryTheory

lemma Quotient.functor_obj_shift [r.IsCompatibleWithShift A] (X : C) (n : A) :
    ((Quotient.functor r).obj X)⟦n⟧ = (Quotient.functor r).obj (X⟦n⟧) := by
  dsimp [Quotient.functor]
  sorry

namespace Quotient

variable [r.IsCompatibleWithShift A] [F.CommShift A]
    (hF : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

variable {r}

-- to be moved
lemma commShiftOfFac_aux {F : Quotient r ⥤ D} {G : C ⥤ D}
    (e : functor r ⋙ F ≅ G) (x y : C) (f₁ f₂ : x ⟶ y)
    (h : r f₁ f₂) : G.map f₁ = G.map f₂ := by
  simp only [← NatIso.naturality_1 e]
  dsimp
  rw [Quotient.sound r h]

noncomputable def commShiftOfFac {F : Quotient r ⥤ D} {G : C ⥤ D}
    (e : functor r ⋙ F ≅ G) [G.CommShift A] : F.CommShift A :=
  letI := liftCommShift G r A (commShiftOfFac_aux e)
  Functor.CommShift.ofIso (Quotient.natIsoLift _
    (lift.isLift r G (commShiftOfFac_aux e) ≪≫ e.symm)) A

lemma natTransCommshift_of_fac {F : Quotient r ⥤ D} {G : C ⥤ D}
    (e : functor r ⋙ F ≅ G) [G.CommShift A] :
    letI := commShiftOfFac A e
    NatTrans.CommShift e.hom A := by
  letI := commShiftOfFac A e
  let iso := lift.isLift r G (commShiftOfFac_aux e)
  let iso' := Quotient.natIsoLift _ (iso ≪≫ e.symm)
  have he (X : C) : e.hom.app X = iso'.inv.app ((functor r).obj X) :=
    (Category.comp_id _).symm
  have := Functor.CommShift.ofIso_compatibility iso' A
  constructor
  intro a
  ext X
  have h₁ := NatTrans.shift_app iso'.inv a ((functor r).obj X)
  have h₂ := NatTrans.shift_app_comm iso.inv a X
  dsimp [iso] at h₁ h₂ ⊢
  simpa [Functor.commShiftIso_comp_hom_app, he, h₁] using h₂.symm

end Quotient

end CategoryTheory
