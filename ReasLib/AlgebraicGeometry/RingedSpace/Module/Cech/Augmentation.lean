module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.Augmentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import ReasLib.Topology.Opens.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Augmented free Čech chains on a ringed space

This leaf is the geometric specialization of the site-generic free Čech chain.  The source-facing
cover is kept as an indexed family of opens together with its supremum equation, while the
underlying chain and its degree-zero augmentation are owned by the generic ringed-site layer.
The homology assertions remain here because their proof uses the extension-by-zero description of
open immersions; they are not consequences of an arbitrary site-theoretic covering predicate.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}} {ι : Type u}

/-- The slice family associated with an indexed open cover of `U`. -/
@[stacks 01EL "ringed-space open cover in the slice"]
abbrev overFamily (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) : ι → Over U :=
  Opens.Cover.overFamily U 𝒰 h𝒰

/-- Lemma 20.10.3 (Tag 01EL): the free Čech chain of an indexed open cover. -/
@[stacks 01EL "ringed-space free Cech chain"]
noncomputable abbrev chain (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) : ChainComplex X.PresheafModules ℕ :=
  SheafOfModules.RingedSite.Cech.freeChain X.ringCatSheaf U
    (overFamily U 𝒰 h𝒰)

/-- Lemma 20.10.3 (Tag 01EL): represented Hom from the free Čech chain. -/
@[stacks 01EL "ringed-space represented Cech Hom functor"]
noncomputable abbrev homFunctor (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) : X.PresheafModules ⥤ CochainComplex AddCommGrpCat ℕ :=
  SheafOfModules.RingedSite.Cech.homFunctor X.ringCatSheaf U
    (overFamily U 𝒰 h𝒰)

/-- Lemma 20.10.3 (Tag 01EL): the underlying additive Čech cochain functor. -/
@[stacks 01EL "ringed-space additive Cech functor"]
noncomputable abbrev additiveComplex (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) : X.PresheafModules ⥤ CochainComplex AddCommGrpCat ℕ :=
  SheafOfModules.RingedSite.Cech.additiveComplex X.ringCatSheaf U
    (overFamily U 𝒰 h𝒰)

/-- Lemma 20.10.3 (Tag 01EL): the canonical Hom-to-Čech natural isomorphism. -/
@[stacks 01EL "ringed-space Hom-to-Cech natural isomorphism"]
noncomputable abbrev comparisonIso (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) : homFunctor U 𝒰 h𝒰 ≅ additiveComplex U 𝒰 h𝒰 :=
  SheafOfModules.RingedSite.Cech.homComparisonIso X.ringCatSheaf U
    (overFamily U 𝒰 h𝒰)

/-- Lemma 20.10.4 (Tag 01EM): the degree-zero augmentation of the free Čech chain. -/
@[stacks 01EM "ringed-space free Cech augmentation"]
noncomputable abbrev augmentation (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) :
    (chain U 𝒰 h𝒰).X 0 ⟶ PresheafOfModules.unit X.ringCatSheaf.obj :=
  SheafOfModules.RingedSite.Cech.augmentation X.ringCatSheaf U
    (overFamily U 𝒰 h𝒰)

/-- Lemma 20.10.4 (Tag 01EM) (1): degree-zero homology is the image of the augmentation. -/
@[stacks 01EM "degree-zero free Cech homology image"]
theorem homology_zero_isomorphic_image (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) :
    IsIsomorphic ((chain U 𝒰 h𝒰).homology 0) (image (augmentation U 𝒰 h𝒰)) := sorry

/-- Lemma 20.10.4 (Tag 01EM) (2): nonzero homology degrees vanish. -/
@[stacks 01EM "positive free Cech homology vanishing"]
theorem homology_isZero_of_ne_zero (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((chain U 𝒰 h𝒰).homology n) := sorry

/-- A successor-degree form of positive free Čech homology vanishing. -/
@[stacks 01EM "successor-degree free Cech homology vanishing"]
theorem homology_succ_isZero (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) (n : ℕ) :
    IsZero ((chain U 𝒰 h𝒰).homology (n + 1)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleCech

end
