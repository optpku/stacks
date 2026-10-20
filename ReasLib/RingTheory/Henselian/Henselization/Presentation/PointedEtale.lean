/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale.AtPrime
public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale.Localization
public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale.Neighborhood
public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.Localization
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.RingHom.IndEtale.Henselian.ResiduePoint

@[expose] public section

/-!
# Pointed-etale presentations of henselizations

This leaf is the neutral presentation interface for a henselization of the
prime localization `Rₚ`. Its objects are the canonical pointed-etale
`R`-algebras over `κ(p)`, and its localized diagram is inherited directly from
`CommAlgCat.Over.Etale.Localization`. The geometric `EtaleNeighborhood`
representation is exposed only as a bridge; it is not a second category owner.

The presentation stores chosen lifts explicitly. Consequently a public
definition never manufactures a non-`Prop` map with `Classical.choose`, while
the colimit assertions remain proposition-valued `Nonempty` statements.

@stack 04GV
-/

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

noncomputable section

namespace IsHenselizationOf.PointedEtale

section Base

variable {R : Type u} [CommRing R]

/-! ### Canonical pointed-etale base -/

/- The prime-indexed category and its two diagrams are owned by the neutral
`CommAlgCat.Over.Etale.AtPrime` leaf.  These source-facing abbreviations retain
the historical namespace without creating a second implementation. -/

/-- Source-facing name for the canonical spectrum point at `p`. -/
@[stacks 04GV "prime point underlying a pointed-etale presentation"]
abbrev basePoint (p : Ideal R) [p.IsPrime] : PrimeSpectrum R :=
  CommAlgCat.Over.Etale.AtPrime.point p

/-- Source-facing name for the prime-indexed pointed-etale category. -/
@[stacks 04GV "canonical pointed-etale category at a prime"]
abbrev category (p : Ideal R) [p.IsPrime] :=
  CommAlgCat.Over.Etale.AtPrime.category p

/-- Source-facing name for the prime-indexed source diagram. -/
@[stacks 04GV "source pointed-etale diagram at a prime"]
noncomputable abbrev sourceDiagram (p : Ideal R) [p.IsPrime] :
    category p ⥤ CommAlgCat R :=
  CommAlgCat.Over.Etale.AtPrime.sourceDiagram p

/-- Source-facing name for the prime-indexed localized diagram. -/
@[stacks 04GV "localized pointed-etale diagram at a prime"]
noncomputable abbrev localizedDiagram (p : Ideal R) [p.IsPrime] :
    category p ⥤ CommAlgCat (Localization.AtPrime p) :=
  CommAlgCat.Over.Etale.AtPrime.localizedDiagram p

/-- Source-facing bridge to the canonical etale-neighborhood representation. -/
@[stacks 04GV "pointed-etale algebra neighborhood bridge"]
noncomputable abbrev neighborhood
    (p : Ideal R) [p.IsPrime] (A : category p) :
    PrimeSpectrum.EtaleNeighborhood (basePoint p) :=
  CommAlgCat.Over.Etale.AtPrime.neighborhood p A

end Base

section Target

variable {R : Type u} [CommRing R]
variable {p : Ideal R} [p.IsPrime]
variable {Rh : Type u} [CommRing Rh]
variable [Algebra (Localization.AtPrime p) Rh]
variable [IsHenselizationOf (Localization.AtPrime p) Rh]

/-! ### A chosen henselization target -/

/-- Restrict the scalar structure of a chosen `Rₚ`-algebra to `R`. This is a
named owner because installing it globally would compete with other `R`
algebra structures on the same target. -/
@[stacks 04GV "source scalar structure of a henselization target"]
noncomputable abbrev sourceAlgebra : Algebra R Rh :=
  Algebra.restrictScalars R (Localization.AtPrime p) Rh

/-- The chosen henselization as an object of `CommAlgCat` over `Rₚ`. -/
@[stacks 04GV "localized henselization target object"]
noncomputable abbrev localizedTarget : CommAlgCat (Localization.AtPrime p) :=
  CommAlgCat.of (Localization.AtPrime p) Rh

/-- The same chosen target viewed as an `R`-algebra by restriction of scalars. -/
@[stacks 04GV "source henselization target object"]
noncomputable def sourceTarget : CommAlgCat R :=
  -- Pin the named restriction-of-scalars owner only while materializing the
  -- categorical target; it is deliberately not registered globally.
  letI : Algebra R Rh := sourceAlgebra (p := p)
  CommAlgCat.of R Rh

/-- Source-facing name for the shared underlying localized pointed-etale map.
The actual instance pin is owned by `CommAlgCat.Over.Target.Localization`. -/
@[stacks 04GV "underlying localized henselization lift"]
noncomputable abbrev ringHom
    (A : category p)
    (f : CommAlgCat.Over.Target.Localization.object
      (Ideal.ker_algebraMap_residueField (I := p)) A.obj ⟶
      localizedTarget (p := p) (Rh := Rh)) :
    Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj) →+* Rh :=
  CommAlgCat.Over.Target.Localization.ringHom
    (Ideal.ker_algebraMap_residueField (I := p)) A.obj f

/-- A localized pointed-etale morphism is a henselian lift when it pulls back
the target maximal ideal to the selected prime. -/
@[stacks 04GV "local pointed-etale henselization lift predicate"]
def IsLift
    (A : category p)
    (f : CommAlgCat.Over.Target.Localization.object
      (Ideal.ker_algebraMap_residueField (I := p)) A.obj ⟶
      localizedTarget (p := p) (Rh := Rh)) : Prop :=
  maximalIdeal (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)) =
    Ideal.comap (ringHom (p := p) A f) (maximalIdeal Rh)

/-- Explicit data for a local lift, including its contracted-prime equation. -/
@[stacks 04GV "chosen local pointed-etale henselization lift"]
structure Lift (A : category p) where
  /-- The selected localized algebra morphism. -/
  hom : CommAlgCat.Over.Target.Localization.object
      (Ideal.ker_algebraMap_residueField (I := p)) A.obj ⟶
    localizedTarget (p := p) (Rh := Rh)
  /-- The selected map contracts the target maximal ideal correctly. -/
  comap_maximalIdeal : IsLift (p := p) A hom

namespace Lift

/-- The defining field of an explicit lift, exposed as a proposition. -/
@[stacks 04GV "specification of a local pointed-etale lift"]
theorem spec {A : category p} (lift : Lift (p := p) (Rh := Rh) A) :
    IsLift (p := p) A lift.hom := sorry

/-- Local lifts of one pointed-etale object to a chosen henselization are
unique. -/
@[stacks 04GV "uniqueness of local pointed-etale henselization lifts"]
theorem unique {A : category p} (lift : Lift (p := p) (Rh := Rh) A)
    (g : CommAlgCat.Over.Target.Localization.object
      (Ideal.ker_algebraMap_residueField (I := p)) A.obj ⟶
      localizedTarget (p := p) (Rh := Rh))
    (hg : IsLift (p := p) A g) : g = lift.hom := sorry

end Lift

/-- The universal local lift from every localized pointed-etale object to a
chosen henselization. -/
@[stacks 04GV "unique localized pointed-etale lift to a henselization"]
theorem existsUnique_lift (A : category p) :
    ∃! f : CommAlgCat.Over.Target.Localization.object
      (Ideal.ker_algebraMap_residueField (I := p)) A.obj ⟶
      localizedTarget (p := p) (Rh := Rh),
      IsLift (p := p) A f := sorry

/-! ### Presentation and cocones -/

/-- A compatible family of chosen local lifts. The family is explicit data;
the shared API does not choose maps behind a non-`Prop` definition. -/
@[stacks 04GV "pointed-etale henselization presentation data"]
structure Presentation where
  /-- A chosen lift at every pointed-etale stage. -/
  lift : ∀ A : category p, Lift (p := p) (Rh := Rh) A
  /-- Naturality of the chosen localized lifts. -/
  naturality : ∀ {A B : category p} (f : A ⟶ B),
    CommAlgCat.Over.Target.Localization.morphism
        (Ideal.ker_algebraMap_residueField (I := p)) f.hom ≫
        (lift B).hom = (lift A).hom

namespace Presentation

/-- The naturality equation in the standard cocone form. -/
@[stacks 04GV "localized pointed-etale presentation naturality"]
theorem cocone_naturality
    {A B : category p}
    (presentation : Presentation (p := p) (Rh := Rh))
    (f : A ⟶ B) :
    (localizedDiagram p).map f ≫ (presentation.lift B).hom =
      (presentation.lift A).hom ≫
        ((Functor.const (category p)).obj
          (localizedTarget (p := p) (Rh := Rh))).map f := sorry

/-- The localized cocone determined by a presentation. -/
@[stacks 04GV "localized pointed-etale henselization cocone"]
noncomputable def cocone (presentation : Presentation (p := p) (Rh := Rh)) :
    Cocone (localizedDiagram p) where
  pt := localizedTarget (p := p) (Rh := Rh)
  ι :=
    { app := fun A => (presentation.lift A).hom
      naturality := fun {_ _} f =>
        cocone_naturality (p := p) (Rh := Rh) presentation f }

/-- The localized cocone is colimiting. The proposition-valued interface avoids
manufacturing `IsColimit` data from deferred proof fields. -/
@[stacks 04GV "localized pointed-etale henselization colimit"]
theorem isColimit (presentation : Presentation (p := p) (Rh := Rh)) :
    Nonempty (IsColimit (cocone (p := p) presentation)) := sorry

/-- Compatibility of the source map with the restricted `R`-algebra structure. -/
@[stacks 04GV "source pointed-etale lift scalar compatibility"]
theorem sourceMap_commutes
    (presentation : Presentation (p := p) (Rh := Rh))
    (A : category p) (r : R) :
      ((ringHom (p := p) A (presentation.lift A).hom).comp
          (algebraMap A.obj.left
            (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj))))
        ((algebraMap R A.obj.left) r) =
        ((algebraMap (Localization.AtPrime p) Rh).comp
          (algebraMap R (Localization.AtPrime p))) r := sorry

/-- The source-diagram map induced by a localized lift. -/
@[stacks 04GV "source pointed-etale henselization lift"]
noncomputable def sourceMap
    (presentation : Presentation (p := p) (Rh := Rh))
    (A : category p) :
    (sourceDiagram p).obj A ⟶ sourceTarget (p := p) (Rh := Rh) :=
  -- Use the same named restriction-of-scalars owner as `sourceTarget`.
  letI : Algebra R Rh := sourceAlgebra (p := p)
  CommAlgCat.ofHom
    { toRingHom :=
        (ringHom (p := p) A (presentation.lift A).hom).comp
          (algebraMap A.obj.left
            (Localization.AtPrime (CommAlgCat.Over.Target.kernel A.obj)))
      commutes' := sourceMap_commutes (p := p) (Rh := Rh) presentation A }

/-- Naturality of the induced source-diagram maps. -/
@[stacks 04GV "source pointed-etale presentation naturality"]
theorem sourceMap_naturality
    {A B : category p}
    (presentation : Presentation (p := p) (Rh := Rh))
    (f : A ⟶ B) :
    (sourceDiagram p).map f ≫ sourceMap (p := p) (Rh := Rh) presentation B =
      sourceMap (p := p) (Rh := Rh) presentation A ≫
        ((Functor.const (category p)).obj
          (sourceTarget (p := p) (Rh := Rh))).map f := sorry

/-- The source cocone obtained by restricting the localized presentation to
the original `R`-algebra diagram. -/
@[stacks 04GV "source pointed-etale henselization cocone"]
noncomputable def sourceCocone
    (presentation : Presentation (p := p) (Rh := Rh)) :
    Cocone (sourceDiagram p) where
  pt := sourceTarget (p := p) (Rh := Rh)
  ι :=
    { app := fun A => sourceMap (p := p) (Rh := Rh) presentation A
      naturality := fun {_ _} f =>
        sourceMap_naturality (p := p) (Rh := Rh) presentation f }

/-- The source cocone is colimiting. -/
@[stacks 04GV "source pointed-etale henselization colimit"]
theorem sourceIsColimit
    (presentation : Presentation (p := p) (Rh := Rh)) :
    Nonempty (IsColimit (sourceCocone (p := p) presentation)) := sorry

end Presentation

/-- Presentation data exist for a chosen henselization target. -/
@[stacks 04GV "existence of pointed-etale henselization presentation"]
theorem exists_presentation :
    Nonempty (Presentation (p := p) (Rh := Rh)) := sorry

end Target

end IsHenselizationOf.PointedEtale
