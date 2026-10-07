module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_17_3_SchemeTheoreticDensity
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf

/-!
# Structure-sheaf characterization of scheme-theoretic density

An open immersion of algebraic spaces is scheme-theoretically dense if and only
if the direct-image structure-sheaf map is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsSchemeTheoreticallyDense

/-- Lemma 67.17.5: Let `S` be a scheme. Let `ι : U ⟶ X` be an open immersion of
algebraic spaces over `S`. Then `U` is scheme-theoretically dense in `X` if and
only if `structureSheafMap ι : 𝒪_X ⟶ ι_* 𝒪_U` is a monomorphism. -/
@[stacks 0836]
theorem iff_mono_structureSheafMap {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔ Mono (structureSheafMap ι) :=
  sorry

/-- Injectivity of `𝒪_X ⟶ ι_* 𝒪_U` implies scheme-theoretic density of the open
immersion. -/
theorem of_mono_structureSheafMap {S : Scheme.{u}} {X U : AlgebraicSpace S}
    {ι : U ⟶ X} [IsOpenImmersion ι] (h : Mono (structureSheafMap ι)) :
    IsSchemeTheoreticallyDense ι :=
  sorry

/-- Scheme-theoretic density of an open immersion implies that
`𝒪_X ⟶ ι_* 𝒪_U` is a monomorphism. -/
instance mono_structureSheafMap {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι] :
    Mono (structureSheafMap ι) :=
  sorry

/-- Scheme-theoretic density of an open immersion is equivalent to vanishing of
the kernel ideal sheaf of `𝒪_X ⟶ ι_* 𝒪_U`. -/
theorem iff_idealSheafSubobject_eq_bot {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔ Hom.idealSheafSubobject ι = ⊥ :=
  sorry

end IsSchemeTheoreticallyDense

end AlgebraicGeometry.AlgebraicSpace
