module

public import stacks_project.Chap67.Lemma_67_13_1_Correspondence

/-!
# Lemma 67.13.1

For a closed immersion of algebraic spaces, `i_* 𝒪_Z` is quasi-coherent,
`i^♯` is surjective, and its kernel is a quasi-coherent ideal sheaf. This
assignment is an inclusion-reversing bijection with closed subspaces, and a
morphism factors through the closed subspace iff the pulled-back ideal map
vanishes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.13.1 (1): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the sheaf `i_* 𝒪_Z` is a quasi-coherent `𝒪_X`-module. -/
@[stacks 03MB]
instance IsClosedImmersion.pushforwardUnit_isQuasicoherent {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z))).IsQuasicoherent :=
  sorry

namespace Hom

/-- Lemma 67.13.1 (2): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the map `i^♯ : 𝒪_X ⟶ i_* 𝒪_Z` is surjective as an `𝒪_X`-module map. -/
@[stacks 03MB]
instance idealSheafMap_epi {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : Epi (idealSheafMap i) :=
  sorry

/-- Lemma 67.13.1 (3): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the kernel of `𝒪_X ⟶ i_* 𝒪_Z` is a quasi-coherent sheaf of ideals. -/
@[stacks 03MB]
theorem idealSheafSubobject_isQuasiCoherent {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : IsQuasiCoherent (idealSheafSubobject i) :=
  sorry

end Hom

namespace ClosedSubspace

/-- Lemma 67.13.1 (4): every quasi-coherent sheaf of ideals on `X` arises as the
kernel ideal sheaf of the closed subspace it cuts out. -/
@[stacks 03MB]
theorem ofQuasiCoherentIdeal_idealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (ofQuasiCoherentIdeal I).idealSheaf = I :=
  sorry

/-- Lemma 67.13.1 (5): closed subspaces of `X` are determined up to isomorphism over
`X` by their kernel ideal sheaves. -/
@[stacks 03MB]
theorem overIso_iff_idealSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z W : ClosedSubspace X) :
    Nonempty (Over.mk Z.ι ≅ Over.mk W.ι) ↔ Z.idealSheaf = W.idealSheaf :=
  sorry

/-- Lemma 67.13.1 (6): the rule sending a closed subspace to its kernel ideal sheaf
is inclusion-reversing. -/
@[stacks 03MB]
theorem idealSheaf_le_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z W : ClosedSubspace X) :
    W.idealSheaf ≤ Z.idealSheaf ↔ ∃ f : Z.X ⟶ W.X, f ≫ W.ι = Z.ι :=
  sorry

end ClosedSubspace

/-- Lemma 67.13.1 (7): a morphism `h : Y ⟶ X` of algebraic spaces factors through a
closed immersion `i : Z ⟶ X` if and only if `h^* I ⟶ 𝒪_Y` is zero, where `I` is
the kernel of `𝒪_X ⟶ i_* 𝒪_Z`. -/
@[stacks 03MB]
theorem IsClosedImmersion.exists_lift_iff_vanishes {S : Scheme.{u}}
    {Y Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (h : Y ⟶ X) :
    (∃ φ : Y ⟶ Z, φ ≫ i = h) ↔ vanishes h (Hom.idealSheafSubobject i) :=
  sorry

/-- A closed immersion is a monomorphism, so a factorization through `Z` is unique
when it exists. -/
theorem IsClosedImmersion.existsUnique_lift_iff_vanishes {S : Scheme.{u}}
    {Y Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (h : Y ⟶ X) :
    (∃! φ : Y ⟶ Z, φ ≫ i = h) ↔ vanishes h (Hom.idealSheafSubobject i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
