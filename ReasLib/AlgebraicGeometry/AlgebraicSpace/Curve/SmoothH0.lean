module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.H0Dim1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

/-!
# Smooth curves with universally trivial structure-sheaf pushforward

The intersection of smoothness with universally trivial structure-sheaf
pushforward and fibres of dimension one is represented by an open of each
family's base. Over a field it admits characterizations by global sections,
geometric connectedness, geometric integrality, and algebraic-closure base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of smooth families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X` and fibres of dimension `1`. -/
def smoothH0 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P) ∧ h0Dim1 S P

/-- Membership in `smoothH0` means `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism after
every base change, including the identity, and the structure morphism is
smooth of relative dimension `1`. -/
theorem smoothH0_iff {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P ↔
      (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
        AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- The `smoothH0` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smoothH0 (S : Scheme.{u}) :
    (smoothH0 S).IsClosedUnderIsomorphisms :=
  sorry

/-- Membership in `𝒞urves^{smooth, h0}` implies membership in
`𝒞urves^{h0, 1}`. -/
theorem smoothH0_le_h0Dim1 {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P → h0Dim1 S P :=
  fun h ↦ h.2

/-- Membership in `𝒞urves^{smooth, h0}` implies smoothness of the structure
morphism. -/
theorem smoothH0_smooth {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P → AlgebraicSpace.Smooth (hom P) :=
  fun h ↦ h.1

/-- For every family of curves, an open of its base represents smoothness,
universally trivial structure-sheaf pushforward, and fibres of dimension one
under every cartesian morphism of families. -/
theorem exists_smoothH0_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      smoothH0 S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- For a proper scheme of dimension at most one over a field, membership in
the smooth locus with universally trivial structure-sheaf pushforward is
equivalent to smoothness of dimension one with bijective canonical map on global
sections, with geometric connectedness, or with geometric integrality, and to
being a smooth curve after base change to an algebraic closure. -/
theorem classifying_factorsThrough_smoothH0_tfae_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    List.TFAE
      [smoothH0 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          Function.Bijective (Scheme.Hom.globalSectionsMap X.hom),
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          GeometricallyConnected X.hom,
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          GeometricallyIntegral X.hom,
        Curve (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) ∧
          AlgebraicGeometry.Smooth (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).hom] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
