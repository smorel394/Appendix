/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Homology.Additive

/-!
# Homology is an additive functor

Addendum to the mathlib file.
-/


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {W : Type*} [Category W] [Preadditive W]
variable {W₁ W₂ : Type*} [Category W₁] [Category W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]
variable {c : ComplexShape ι} {C D : HomologicalComplex V c}
variable (f : C ⟶ D) (i : ι)

namespace CategoryTheory

instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [F.Faithful] :
    (F.mapHomologicalComplex c).Faithful where
  map_injective {K L} f₁ f₂ h := by
    ext n
    apply F.map_injective
    exact (HomologicalComplex.eval W c n).congr_map h

instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [F.Faithful] [F.Full] :
    (F.mapHomologicalComplex c).Full where
  map_surjective {X Y} f := ⟨
    { f := fun n => F.preimage (f.f n)
      comm' := by
        intro i j _
        apply F.map_injective
        dsimp
        simp only [Functor.map_comp, Functor.map_preimage]
        exact f.comm i j }, by aesop_cat⟩

@[simps!]
def Functor.mapHomologicalComplexCompIso {W' : Type*} [Category W'] [Preadditive W']
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι) :
    H.mapHomologicalComplex c ≅ F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex e.symm c

end CategoryTheory
