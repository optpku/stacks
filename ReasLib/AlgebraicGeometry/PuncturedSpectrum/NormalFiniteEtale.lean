/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.FiniteNormalAlgebra
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtale

/-!
# Finite etale covers of a normal punctured spectrum

This file packages the global-sections functor and its extension criterion for
Noetherian normal local rings of dimension at least two.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Pullback on global sections, viewed as an algebra morphism over the base. -/
theorem globalSectionsAlgHom_commutes
    {V W : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)} (f : V ⟶ W) :
    ∀ r : A,
      (Scheme.Γ.map f.left.op).hom
          (@algebraMap A (Scheme.globalSectionsRing W.left) _ _
            (Scheme.Hom.globalSectionsAlgebra (W.hom ≫ (puncturedOpen A).ι)) r) =
        @algebraMap A (Scheme.globalSectionsRing V.left) _ _
          (Scheme.Hom.globalSectionsAlgebra (V.hom ≫ (puncturedOpen A).ι)) r := sorry

/-- A morphism of finite etale covers induces the contravariant algebra morphism on global sections. -/
noncomputable def globalSectionsAlgHom
    {V W : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)} (f : V ⟶ W) :
    Scheme.Hom.globalSectionsAlg (W.hom ≫ (puncturedOpen A).ι) ⟶
      Scheme.Hom.globalSectionsAlg (V.hom ≫ (puncturedOpen A).ι) :=
  let sourceAlgebra :=
    Scheme.Hom.globalSectionsAlgebra (W.hom ≫ (puncturedOpen A).ι)
  let targetAlgebra :=
    Scheme.Hom.globalSectionsAlgebra (V.hom ≫ (puncturedOpen A).ι)
  let map :=
    @AlgHom.mk A (Scheme.globalSectionsRing W.left) (Scheme.globalSectionsRing V.left)
      inferInstance inferInstance inferInstance sourceAlgebra targetAlgebra
      (Scheme.Γ.map f.left.op).hom (globalSectionsAlgHom_commutes f)
  @CommAlgCat.ofHom A inferInstance _ _ inferInstance sourceAlgebra inferInstance targetAlgebra map

/-- The underlying ring map is the morphism on global sections. -/
theorem globalSectionsAlgHom_hom
    {V W : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)} (f : V ⟶ W) :
    (globalSectionsAlgHom f).hom.toRingHom = (Scheme.Γ.map f.left.op).hom := rfl

/-- Pullback along an identity cover is the identity algebra morphism. -/
theorem globalSectionsAlgHom_id
    {V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)} :
    globalSectionsAlgHom (𝟙 V) = 𝟙 (Scheme.Hom.globalSectionsAlg
      (V.hom ≫ (puncturedOpen A).ι)) := sorry

/-- Pullback on global sections reverses composition. -/
theorem globalSectionsAlgHom_comp
    {V W Z : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)} (f : V ⟶ W) (g : W ⟶ Z) :
    globalSectionsAlgHom (f ≫ g) = globalSectionsAlgHom g ≫ globalSectionsAlgHom f := sorry

/-- Global sections of a finite etale punctured cover define a finite normal torsion-free algebra. -/
theorem globalSections_mem [IsNoetherianRing A] [IsNormalRing A]
    (h_dimension : 2 ≤ ringKrullDim A)
    (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)) :
    CommAlgCat.finiteNormalTorsionFreeEtaleOver A (puncturedOpen A)
      (Scheme.Hom.globalSectionsAlg (V.hom ≫ (puncturedOpen A).ι)) := sorry

/-- The global-sections functor takes finite etale covers to the opposite corrected algebra category. -/
noncomputable def globalSections [IsNoetherianRing A] [IsNormalRing A]
    (h_dimension : 2 ≤ ringKrullDim A) :
    Scheme.FiniteEtale (PuncturedSpectrum.scheme A) ⥤
      (CommAlgCat.FiniteNormalTorsionFreeEtaleOver A (puncturedOpen A))ᵒᵖ where
  obj V := Opposite.op
    { obj := Scheme.Hom.globalSectionsAlg (V.hom ≫ (puncturedOpen A).ι)
      property := globalSections_mem h_dimension V }
  map f := (ObjectProperty.homMk (globalSectionsAlgHom f)).op
  map_id := by
    intro V
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact globalSectionsAlgHom_id
  map_comp := by
    intro V W Z f g
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact globalSectionsAlgHom_comp f g

variable [IsNoetherianRing A] [IsNormalRing A]

/-- The object assigned by the global-sections functor is the bundled global-sections algebra. -/
theorem globalSections_obj (h_dimension : 2 ≤ ringKrullDim A)
    (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)) :
    ((globalSections h_dimension).obj V).unop.obj =
      Scheme.Hom.globalSectionsAlg (V.hom ≫ (puncturedOpen A).ι) := rfl

/-- The morphism assigned by the global-sections functor is induced by pullback on sections. -/
theorem globalSections_map (h_dimension : 2 ≤ ringKrullDim A)
    {V W : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)} (f : V ⟶ W) :
    ((globalSections h_dimension).map f).unop.hom = globalSectionsAlgHom f := rfl

/-- Global sections of a finite etale punctured cover are torsion-free over the base. -/
theorem globalSections_torsionFree
    (h_dimension : 2 ≤ ringKrullDim A)
    (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)) :
    Module.IsTorsionFree A (Scheme.Hom.globalSectionsAlg (V.hom ≫ (puncturedOpen A).ι)) :=
  ((globalSections h_dimension).obj V).unop.property.2

/-- Global sections give an equivalence with the opposite corrected finite-normal algebra category. -/
instance globalSections_isEquivalence (h_dimension : 2 ≤ ringKrullDim A) :
    (globalSections h_dimension).IsEquivalence := sorry

end AlgebraicGeometry.PuncturedSpectrum

namespace AlgebraicGeometry.Scheme.Hom

/-- Finite etale extension across the closed point is characterized by finite etaleness of global sections. -/
theorem finiteEtale_punctured_extension_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalRing A]
    (h_dimension : 2 ≤ ringKrullDim A)
    (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)) :
    let X : Scheme := Spec (CommRingCat.of A)
    let U : X.Opens := PuncturedSpectrum.puncturedOpen A
    let B : CommAlgCat A := Scheme.Hom.globalSectionsAlg (V.hom ≫ U.ι)
    (∃ Y : Scheme.FiniteEtale X,
        Nonempty ((Scheme.finiteEtaleBaseChange U.ι).obj Y ≅ V)) ↔
      CommAlgCat.finiteEtale A B := sorry

end AlgebraicGeometry.Scheme.Hom
