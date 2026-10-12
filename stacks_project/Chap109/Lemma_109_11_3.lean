/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.Clopen
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import stacks_project.Chap109.Lemma_109_11_3_Substack

/-!
# Geometrically reduced and connected curves of a given genus

There is a decomposition of `𝒞urves^{grc, 1}` into open-and-closed
substacks `𝒞urves^{grc, 1}_g` for `g ≥ 0`, witnessed on families by a
pairwise-disjoint clopen cover of the base, classifying families of
curves with reduced, connected geometric fibres of dimension `1` for
which `R¹ f_* 𝒪_X` is locally free of rank `g`, equivalently proper
geometrically reduced geometrically connected schemes of dimension `1`
over a field with genus `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.11.3 (1): the geometrically reduced connected dimension-`1` locus
`𝒞urves^{grc, 1}` decomposes as the coproduct of open-and-closed substacks
`𝒞urves^{grc, 1}_g` for `g ≥ 0`: a family lies in `𝒞urves^{grc, 1}` if and
only if its base admits a pairwise-disjoint clopen cover `(U_g)_{g : ℕ}`,
with pieces possibly empty, such that the base change to each `U_g` lies in
`𝒞urves^{grc, 1}_g`. -/
@[stacks 0E1K]
theorem geometricallyReducedConnectedDim1_iff_clopenCover
    {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1 S P ↔
      ∃ U : ℕ → (base P).left.Opens,
        iSup U = ⊤ ∧
          Pairwise (fun g g' ↦
              Disjoint (U g : Set (base P).left) (U g')) ∧
            (∀ g, IsClopen (U g : Set (base P).left)) ∧
              ∀ g, geometricallyReducedConnectedDim1OfGenus g S
                (baseChangeToOpen P (U g)) :=
  sorry

/-- Lemma 109.11.3 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{grc, 1}_g` if and only if the
geometric fibres of `X ⟶ S` are reduced, connected, of dimension `1`, and
`R¹ f_* 𝒪_X` is a locally free `𝒪_S`-module of rank `g`. -/
@[stacks 0E1K]
theorem classifying_factorsThrough_geometricallyReducedConnectedDim1OfGenus_iff
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      Hom.HasReducedGeometricFibres (hom P) ∧
        Hom.HasConnectedGeometricFibres (hom P) ∧
          (∀ ybar : GeometricPoint (ofOver (base P)),
              dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1) ∧
            SheafOfModules.IsFiniteLocallyFreeOfRank g
              (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.11.3 (3): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{grc, 1}_g` if and only if `X` is geometrically reduced,
geometrically connected, has dimension `1`, and has genus `g`. -/
@[stacks 0E1K]
theorem classifying_factorsThrough_geometricallyReducedConnectedDim1OfGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    geometricallyReducedConnectedDim1OfGenus g (Spec (CommRingCat.of k))
        (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.geometricallyReduced X ∧
        GeometricallyConnected X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
