/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_20_8_Over
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Definition_76_6_5_Symmetric

/-!
# Normal cones and normal bundles of immersions of algebraic spaces

The normal cone of an immersion of algebraic spaces is the relative spectrum of its
total conormal algebra. The normal bundle is the relative spectrum of the symmetric
algebra of its conormal sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A morphism of quasi-coherent `𝒪_X`-algebras induces a morphism of relative spectra
in the opposite direction, by postcomposition on functor-of-points algebra maps. -/
noncomputable def relativeSpecMap {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) : relativeSpec B ⟶ relativeSpec A where
  app T :=
    TypeCat.ofHom fun p : relativeSpectrumPair B T.unop =>
      ⟨p.1, ⟨restrictUnderMap f.hom ≫ p.2.1, sorry⟩⟩
  naturality := sorry

/-- The first component of `relativeSpecMap f` is the same morphism to `X`. -/
theorem relativeSpecMap_fst {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) (T : (Over S)ᵒᵖ) (p : relativeSpectrumPair B T.unop) :
    ((relativeSpecMap f).app T p).1 = p.1 :=
  sorry

/-- The algebra map of `relativeSpecMap f` is postcomposition with `restrictUnderMap f`. -/
theorem relativeSpecMap_snd {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) (T : (Over S)ᵒᵖ) (p : relativeSpectrumPair B T.unop) :
    ((relativeSpecMap f).app T p).2.1 =
      restrictUnderMap f.hom ≫ p.2.1 :=
  sorry

/-- `relativeSpecMap` is compatible with the structure morphisms to `X`. -/
theorem relativeSpecMap_comp_π {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (f : A ⟶ B) :
    relativeSpecMap f ≫ relativeSpecπ A = relativeSpecπ B :=
  sorry

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The normal cone of an immersion of algebraic spaces over `S`. -/
noncomputable def normalCone : AlgebraicSpace S :=
  relativeSpec (ConormalAlgebra.total i)

/-- The normal cone is the relative spectrum of the total conormal algebra. -/
theorem normalCone_eq_relativeSpec :
    normalCone i = relativeSpec (ConormalAlgebra.total i) :=
  rfl

/-- The structural morphism from the normal cone of an immersion to its source. -/
noncomputable def normalConeπ : normalCone i ⟶ Z :=
  relativeSpecπ (ConormalAlgebra.total i)

/-- The structure morphism of the normal cone is the relative-spectrum projection of
the total conormal algebra. -/
theorem normalConeπ_eq :
    normalConeπ i = relativeSpecπ (ConormalAlgebra.total i) :=
  rfl

/-- The structure morphism of the normal cone is affine. -/
instance instAffine_normalConeπ : Affine (normalConeπ i) :=
  instAffine_relativeSpecπ (ConormalAlgebra.total i)

/-- The normal bundle of an immersion of algebraic spaces over `S`. -/
noncomputable def normalBundle : AlgebraicSpace S :=
  relativeSpec (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i))

/-- The normal bundle is the relative spectrum of the symmetric algebra of the
conormal sheaf. -/
theorem normalBundle_eq_relativeSpec :
    normalBundle i =
      relativeSpec (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)) :=
  rfl

/-- The structural morphism from the normal bundle of an immersion to its source. -/
noncomputable def normalBundleπ : normalBundle i ⟶ Z :=
  relativeSpecπ (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i))

/-- The structure morphism of the normal bundle is the relative-spectrum projection of
the symmetric algebra of the conormal sheaf. -/
theorem normalBundleπ_eq :
    normalBundleπ i =
      relativeSpecπ (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)) :=
  rfl

/-- The structure morphism of the normal bundle is affine. -/
instance instAffine_normalBundleπ : Affine (normalBundleπ i) :=
  instAffine_relativeSpecπ (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i))


end AlgebraicGeometry.AlgebraicSpace
