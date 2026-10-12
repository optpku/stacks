/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Derived Chow presentations

This file packages the local projective-space diagram and supported derived module supplied by
the derived form of Chow's lemma.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A derived Chow presentation at `x` consists of local projective-space data, a closed
subscheme with the prescribed behavior over the chosen opens, and a pseudo-coherent derived
module supported on that closed subscheme. -/
structure DerivedChowPresentation {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (x : X) where
  /-- The dimension of the chosen relative projective space. -/
  n : ℕ
  /-- The chosen relative projective space over `Spec (CommRingCat.of A)`. -/
  P : ProjectiveSpaceOver (Spec (CommRingCat.of A)) n
  /-- The open neighborhood of the distinguished point. -/
  U : X.Opens
  /-- The chosen open of the relative projective space. -/
  V : P.scheme.Opens
  /-- The ideal sheaf defining the closed subscheme of the ambient pullback. -/
  I : (pullback f P.hom).IdealSheafData
  /-- The distinguished point of the closed subscheme. -/
  z : I.subscheme
  /-- The derived module on the ambient pullback. -/
  E : RingedSpace.ModuleDerived (pullback f P.hom).toRingedSpace
  /-- The distinguished point belongs to the chosen source open. -/
  pointMemSourceOpen : x ∈ U
  /-- The canonical immersion of the closed subscheme is of finite presentation. -/
  immersionFinitePresentation : Scheme.Hom.FinitePresentation I.subschemeι
  /-- The source projection is an isomorphism over the chosen source open. -/
  isIsoOverSourceOpen :
    IsIso ((I.subschemeι ≫ pullback.fst f P.hom) ∣_ U)
  /-- The source projection carries the distinguished point to `x`. -/
  sourceProjectionPoint :
    (I.subschemeι ≫ pullback.fst f P.hom).base z = x
  /-- The projective-space projection is a closed immersion over the chosen projective open. -/
  isClosedImmersionOverProjectiveOpen :
    IsClosedImmersion ((I.subschemeι ≫ pullback.snd f P.hom) ∣_ V)
  /-- The source and projective opens have the same preimage in the closed subscheme. -/
  preimageSourceOpen_eq_preimageProjectiveOpen :
    (I.subschemeι ≫ pullback.fst f P.hom) ⁻¹ᵁ U =
      (I.subschemeι ≫ pullback.snd f P.hom) ⁻¹ᵁ V
  /-- The projective-space projection of the distinguished point belongs to the chosen open. -/
  projectiveProjectionPointMem :
    (I.subschemeι ≫ pullback.snd f P.hom).base z ∈ V
  /-- Over the chosen projective open, the derived module is the degree-zero pushforward of the
  structure sheaf of the closed subscheme. -/
  restrictionIso :
    let Y := pullback f P.hom
    let i := I.subschemeι
    let W := pullback.snd f P.hom ⁻¹ᵁ V
    (RingedSpace.moduleRestrictionToOpenDerived Y.toRingedSpace W).obj E ≅
      (RingedSpace.moduleRestrictionToOpenDerived Y.toRingedSpace W).obj
        (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
  /-- The derived module is pseudo-coherent. -/
  pseudoCoherent : RingedSpace.ModuleDerived.IsPseudoCoherent E
  /-- The derived module is supported on the chosen closed subscheme. -/
  supportedOn : RingedSpace.ModuleDerived.IsSupportedOn E I.support

namespace DerivedChowPresentation

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of A)} {x : X}

/-- The ambient fiber product of a derived Chow presentation. -/
def ambient (M : DerivedChowPresentation f x) : Scheme.{u} :=
  pullback f M.P.hom

/-- The canonical closed immersion into the ambient fiber product. -/
def immersion (M : DerivedChowPresentation f x) : M.I.subscheme ⟶ M.ambient :=
  M.I.subschemeι

/-- The projection from the closed subscheme to the source scheme. -/
def sourceProjection (M : DerivedChowPresentation f x) : M.I.subscheme ⟶ X :=
  M.immersion ≫ pullback.fst f M.P.hom

/-- The projection from the closed subscheme to the relative projective space. -/
def projectiveProjection (M : DerivedChowPresentation f x) : M.I.subscheme ⟶ M.P.scheme :=
  M.immersion ≫ pullback.snd f M.P.hom

/-- The preimage in the ambient fiber product of the chosen projective open. -/
def projectiveOpenPreimage (M : DerivedChowPresentation f x) : M.ambient.Opens :=
  pullback.snd f M.P.hom ⁻¹ᵁ M.V

/-- Constructs a derived Chow presentation from an explicit closed-subscheme diagram, its local
projection properties, and a supported pseudo-coherent derived module. -/
def ofComponents (n : ℕ) (P : ProjectiveSpaceOver (Spec (CommRingCat.of A)) n)
    (U : X.Opens) (V : P.scheme.Opens) (I : (pullback f P.hom).IdealSheafData)
    (z : I.subscheme) (E : RingedSpace.ModuleDerived (pullback f P.hom).toRingedSpace)
    (pointMemSourceOpen : x ∈ U)
    (immersionFinitePresentation : Scheme.Hom.FinitePresentation I.subschemeι)
    (isIsoOverSourceOpen : IsIso ((I.subschemeι ≫ pullback.fst f P.hom) ∣_ U))
    (sourceProjectionPoint : (I.subschemeι ≫ pullback.fst f P.hom).base z = x)
    (isClosedImmersionOverProjectiveOpen :
      IsClosedImmersion ((I.subschemeι ≫ pullback.snd f P.hom) ∣_ V))
    (preimageSourceOpen_eq_preimageProjectiveOpen :
      (I.subschemeι ≫ pullback.fst f P.hom) ⁻¹ᵁ U =
        (I.subschemeι ≫ pullback.snd f P.hom) ⁻¹ᵁ V)
    (projectiveProjectionPointMem :
      (I.subschemeι ≫ pullback.snd f P.hom).base z ∈ V)
    (restrictionIso :
      let Y := pullback f P.hom
      let i := I.subschemeι
      let W := pullback.snd f P.hom ⁻¹ᵁ V
      (RingedSpace.moduleRestrictionToOpenDerived Y.toRingedSpace W).obj E ≅
        (RingedSpace.moduleRestrictionToOpenDerived Y.toRingedSpace W).obj
          (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj)
    (pseudoCoherent : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    (supportedOn : RingedSpace.ModuleDerived.IsSupportedOn E I.support) :
    DerivedChowPresentation f x where
  n := n
  P := P
  U := U
  V := V
  I := I
  z := z
  E := E
  pointMemSourceOpen := pointMemSourceOpen
  immersionFinitePresentation := immersionFinitePresentation
  isIsoOverSourceOpen := isIsoOverSourceOpen
  sourceProjectionPoint := sourceProjectionPoint
  isClosedImmersionOverProjectiveOpen := isClosedImmersionOverProjectiveOpen
  preimageSourceOpen_eq_preimageProjectiveOpen :=
    preimageSourceOpen_eq_preimageProjectiveOpen
  projectiveProjectionPointMem := projectiveProjectionPointMem
  restrictionIso := restrictionIso
  pseudoCoherent := pseudoCoherent
  supportedOn := supportedOn

/-- The defining conditions of a derived Chow presentation are the prescribed local behavior of
the two projections and a supported pseudo-coherent derived module with the stated restriction. -/
theorem conditions_spec (M : DerivedChowPresentation f x) :
    x ∈ M.U ∧ Scheme.Hom.FinitePresentation M.immersion ∧
      IsIso (M.sourceProjection ∣_ M.U) ∧ M.sourceProjection.base M.z = x ∧
      IsClosedImmersion (M.projectiveProjection ∣_ M.V) ∧
      M.sourceProjection ⁻¹ᵁ M.U = M.projectiveProjection ⁻¹ᵁ M.V ∧
      M.projectiveProjection.base M.z ∈ M.V ∧
      Nonempty
        ((RingedSpace.moduleRestrictionToOpenDerived M.ambient.toRingedSpace
              M.projectiveOpenPreimage).obj M.E ≅
          (RingedSpace.moduleRestrictionToOpenDerived M.ambient.toRingedSpace
              M.projectiveOpenPreimage).obj
            (Scheme.DerivedQCoh.pushforwardStructureSheaf M.I.subschemeι).obj) ∧
      RingedSpace.ModuleDerived.IsPseudoCoherent M.E ∧
      RingedSpace.ModuleDerived.IsSupportedOn M.E M.I.support := sorry

/-- A separated finitely presented scheme over a commutative ring admits a derived Chow
presentation at every point. -/
theorem exists_of_separated_finitePresentation
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [Scheme.Hom.FinitePresentation f] (x : X) :
    Nonempty (DerivedChowPresentation f x) := sorry

end DerivedChowPresentation

end AlgebraicGeometry
