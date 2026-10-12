/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.AlongDerived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Coreflection

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The coherator on the scheme carried by a compact open subset of a qcqs scheme. -/
noncomputable def openCoherator (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (W : CompactOpens X) :
    RingedSpace.ModuleDerived (Scheme.Opens.toScheme W.toOpens).toRingedSpace ⥤
      Scheme.ModuleDerived.Quasicoherent (Scheme.Opens.toScheme W.toOpens) :=
  -- Local instance justification (proof-local temporary data): compactness is carried by `W`.
  letI : CompactSpace W.toOpens := isCompact_iff_compactSpace.mp W.isCompact
  -- Local instance justification (proof-local temporary data): an open subspace of `X` is qcqs.
  letI : QuasiSeparatedSpace W.toOpens :=
    QuasiSeparatedSpace.of_isOpenEmbedding W.toOpens.isOpen.isOpenEmbedding_subtypeVal
  (Scheme.ModuleDerived.Quasicoherent.inclusion
    (Scheme.Opens.toScheme W.toOpens)).rightAdjoint

/-- Restriction to a compact open, followed by its coherator and derived pushforward back to
the ambient scheme. -/
noncomputable def openPushforwardCoherator (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (W : CompactOpens X) :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤ Scheme.ModuleDerived.Quasicoherent X :=
  -- Local instance justification (proof-local temporary data): compactness is carried by `W`.
  letI : CompactSpace W.toOpens := isCompact_iff_compactSpace.mp W.isCompact
  -- Local instance justification (proof-local temporary data): an open subspace of `X` is qcqs.
  letI : QuasiSeparatedSpace W.toOpens :=
    QuasiSeparatedSpace.of_isOpenEmbedding W.toOpens.isOpen.isOpenEmbedding_subtypeVal
  RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace W.toOpens ⋙
    openCoherator X W ⋙ pushforwardCohomologyIn (Scheme.Opens.ι W.toOpens)

/-- Applying the coherator after derived pushforward along the identity does not change an
object, up to isomorphism. -/
theorem rightAdjoint_identityPushforward_obj_isomorphic (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsIsomorphic
      ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj
        ((RingedSpace.moduleDerivedPushforward (𝟙 X.toRingedSpace)).obj K))
      ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K) := sorry

/-- Applying the ambient coherator after derived restriction and pushforward along a compact
open is objectwise isomorphic to restriction, the open coherator, and quasicoherent
pushforward. -/
theorem rightAdjoint_alongDerived_obj_isomorphic (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (W : CompactOpens X)
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsIsomorphic
      ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj
        ((RingedSpace.OpenSubspace.Pushforward.alongDerived
          (𝟙 X.toRingedSpace) W.toOpens).obj K))
      ((openPushforwardCoherator X W).obj K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
