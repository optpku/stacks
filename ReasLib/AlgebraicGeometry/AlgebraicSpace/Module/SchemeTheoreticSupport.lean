/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Scheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Annihilator
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport

/-!
# Scheme-theoretic support of modules on algebraic spaces

The scheme-theoretic support is the least closed subspace carrying a
quasi-coherent module with the prescribed pushforward. For finite-type
quasi-coherent modules it exists and agrees with scheme support on étale charts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The scheme-theoretic support of the restriction to a scheme `U` of an étale
pullback of an `𝒪_X`-module. -/
def etalePullbackSchemeTheoreticSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (F : X.Modules) (φ : ofOver U ⟶ X) : U.left.IdealSheafData :=
  Scheme.Modules.schemeTheoreticSupport ((restrictToScheme U).obj ((pullback φ).obj F))

/-- `etalePullbackSchemeTheoreticSupport F φ` is the scheme-theoretic support of
the restriction of `φ* F` to `U`. -/
theorem etalePullbackSchemeTheoreticSupport_eq {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (F : X.Modules) (φ : ofOver U ⟶ X) :
    etalePullbackSchemeTheoreticSupport F φ =
      Scheme.Modules.schemeTheoreticSupport
        ((restrictToScheme U).obj ((pullback φ).obj F)) :=
  rfl

/-- A closed immersion `i : Z ⟶ X` is a scheme-theoretic support of `F` if `F`
is the pushforward of a quasi-coherent `𝒪_Z`-module and `i` is least among
closed immersions with that property. -/
class IsSchemeTheoreticSupport {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) (i : Z ⟶ X) : Prop where
  /-- The comparison `i : Z ⟶ X` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i
  /-- There is a quasi-coherent `𝒪_Z`-module whose pushforward is isomorphic to `F`. -/
  exists_quasicoherent :
    ∃ G : Z.Modules, G.IsQuasicoherent ∧ Nonempty ((pushforward i).obj G ≅ F)
  /-- Any other closed immersion through which `F` is a quasi-coherent pushforward
  admits a unique comparison from `Z`. -/
  exists_lift {Z' : AlgebraicSpace S} (i' : Z' ⟶ X) [IsClosedImmersion i']
      (h : ∃ G' : Z'.Modules,
        G'.IsQuasicoherent ∧ Nonempty ((pushforward i').obj G' ≅ F)) :
      ∃! k : Z ⟶ Z', k ≫ i' = i

/-- A morphism `i : Z ⟶ X` is a scheme-theoretic support of `F` if and only if it
is a least closed immersion through which `F` is a quasi-coherent pushforward. -/
theorem isSchemeTheoreticSupport_iff {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) (i : Z ⟶ X) :
    IsSchemeTheoreticSupport F i ↔
      IsClosedImmersion i ∧
        (∃ G : Z.Modules, G.IsQuasicoherent ∧ Nonempty ((pushforward i).obj G ≅ F)) ∧
          ∀ {Z' : AlgebraicSpace S} (i' : Z' ⟶ X) [IsClosedImmersion i'],
            (∃ G' : Z'.Modules,
              G'.IsQuasicoherent ∧ Nonempty ((pushforward i').obj G' ≅ F)) →
              ∃! k : Z ⟶ Z', k ≫ i' = i :=
  sorry

namespace IsSchemeTheoreticSupport

/-- A least closed-subspace factorization through which `F` is a quasi-coherent
pushforward is a scheme-theoretic support. -/
theorem of_isLeast_closedSubspace {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (Z : ClosedSubspace X)
    (hQC : ∃ G : Z.X.Modules,
      G.IsQuasicoherent ∧ Nonempty ((pushforward Z.ι).obj G ≅ F))
    (hleast : ∀ Z' : ClosedSubspace X,
      (∃ G' : Z'.X.Modules,
        G'.IsQuasicoherent ∧ Nonempty ((pushforward Z'.ι).obj G' ≅ F)) →
        ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι) :
    IsSchemeTheoreticSupport F Z.ι :=
  sorry

end IsSchemeTheoreticSupport

/-- Every finite-type quasi-coherent module on an algebraic space is the pushforward
of a quasi-coherent module from a smallest closed subspace. -/
theorem exists_schemeTheoreticSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X), IsSchemeTheoreticSupport F i :=
  sorry

/-- There exists a least closed subspace of `X` through which `F` is a
quasi-coherent pushforward. -/
theorem exists_least_closedSubspace {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ Z : ClosedSubspace X,
      (∃ G : Z.X.Modules,
        G.IsQuasicoherent ∧ Nonempty ((pushforward Z.ι).obj G ≅ F)) ∧
        ∀ Z' : ClosedSubspace X,
          (∃ G' : Z'.X.Modules,
            G'.IsQuasicoherent ∧ Nonempty ((pushforward Z'.ι).obj G' ≅ F)) →
            ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι :=
  sorry

/-- The inverse image of a scheme-theoretic support under an étale morphism from a
scheme is a scheme-theoretic support of the pulled-back module. -/
@[instance]
theorem isSchemeTheoreticSupport_inverseImage_etale {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    IsSchemeTheoreticSupport ((pullback φ).obj F) (inverseImageι φ i) :=
  sorry

/-- Under an étale morphism from a scheme, the inverse image of a
scheme-theoretic support of `F` is uniquely isomorphic over `ofOver U` to the
algebraic space of the scheme-theoretic support of the restriction of `φ* F`. -/
theorem inverseImage_etale_iso_schemeTheoreticSupport {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    ∃! e : inverseImage φ i ≅
        ofOverClosedSubscheme U (etalePullbackSchemeTheoreticSupport F φ),
      e.hom ≫ ofOverClosedSubschemeι U (etalePullbackSchemeTheoreticSupport F φ) =
        inverseImageι φ i :=
  sorry

/-- A quasi-coherent module on a scheme-theoretic support whose pushforward is
isomorphic to a finite-type quasi-coherent module is of finite type. -/
theorem isFiniteType_of_pushforward_iso {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) : G.IsFiniteType :=
  sorry

/-- The support of a finite-type quasi-coherent module is the image of the points
of its scheme-theoretic support. -/
theorem moduleSupport_eq_pointsSet {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsSchemeTheoreticSupport F i] :
    moduleSupport F = ClosedSubspace.pointsSet (ClosedSubspace.ofι i) :=
  sorry

/-- The support of a quasi-coherent descent `G` of `F` along a scheme-theoretic
support is all of `|Z|`. -/
theorem moduleSupport_eq_univ_of_pushforward_iso {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) :
    moduleSupport G = (Set.univ : Set (Points Z)) :=
  sorry

/-- The scheme-theoretic support of a finite-type quasi-coherent `𝒪_X`-module is
the closed subspace of `X` cut out by the annihilator ideal. -/
def schemeTheoreticSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (annihilatorIdeal F)

/-- The inclusion of the scheme-theoretic support is the closed-subspace
inclusion cut out by the annihilator ideal. -/
theorem schemeTheoreticSupport_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (schemeTheoreticSupport F).ι = subschemeι (annihilatorIdeal F) :=
  rfl

/-- The inclusion of the scheme-theoretic support of `F` is a least closed
immersion through which `F` is a quasi-coherent pushforward. -/
instance instIsSchemeTheoreticSupport_schemeTheoreticSupport {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    IsSchemeTheoreticSupport F (schemeTheoreticSupport F).ι :=
  sorry

/-- The scheme-theoretic support of `F` is the closed subspace cut out by
`annihilatorIdeal F`, and its inclusion is a least closed immersion through
which `F` is a quasi-coherent pushforward. -/
theorem schemeTheoreticSupport_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    IsSchemeTheoreticSupport F (schemeTheoreticSupport F).ι ∧
      (schemeTheoreticSupport F).ι = subschemeι (annihilatorIdeal F) ∧
        annihilatorIdeal F = Subobject.mk (annihilatorι F) :=
  ⟨instIsSchemeTheoreticSupport_schemeTheoreticSupport F,
    schemeTheoreticSupport_ι F, annihilatorIdeal_eq F⟩

/-- Any scheme-theoretic support of `F` is uniquely isomorphic over `X` to the
chosen scheme-theoretic support. -/
theorem existsUnique_iso_schemeTheoreticSupport {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i] :
    ∃! e : Z ≅ (schemeTheoreticSupport F).X,
      e.hom ≫ (schemeTheoreticSupport F).ι = i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
