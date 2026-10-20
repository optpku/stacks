/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.ExcisionProperties
import StacksCheckRecall

/-!
# Transport of morphism properties across excision for modifications

Under the correspondence of Lemma 70.19.1, a morphism `g : X ⟶ W` that is an
isomorphism over the complementary open of `i` is quasi-compact, quasi-separated,
separated, locally of finite presentation, of finite presentation, locally of
finite type, of finite type, proper, integral, or finite if and only if the
corresponding morphism `h : Y ⟶ V` is.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.19.2: quasi-compact morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.quasiCompact_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    QuasiCompact X.obj.hom ↔ QuasiCompact (overPullbackSnd f X.obj))

/- Lemma 70.19.2: quasi-separated morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.quasiSeparated_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    QuasiSeparated X.obj.hom ↔ QuasiSeparated (overPullbackSnd f X.obj))

/- Lemma 70.19.2: separated morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.separated_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    Separated X.obj.hom ↔ Separated (overPullbackSnd f X.obj))

/- Lemma 70.19.2: locally of finite presentation morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.locallyOfFinitePresentation_hom_iff :
    ∀ {S : Scheme.{u}}
    {V W T : AlgebraicSpace S} (f : V ⟶ W) [Etale f] [Separated f]
    (i : T ⟶ W) [IsClosedImmersion i] [IsIso (inverseImageTo f i)]
    (X : IsoOverOpen (closedImmersionComplementι i)),
    LocallyOfFinitePresentation X.obj.hom ↔
      LocallyOfFinitePresentation (overPullbackSnd f X.obj))

/- Lemma 70.19.2: of finite presentation morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.finitePresentation_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    FinitePresentation X.obj.hom ↔ FinitePresentation (overPullbackSnd f X.obj))

/- Lemma 70.19.2: locally of finite type morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.locallyOfFiniteType_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    LocallyOfFiniteType X.obj.hom ↔ LocallyOfFiniteType (overPullbackSnd f X.obj))

/- Lemma 70.19.2: of finite type morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.finiteType_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    FiniteType X.obj.hom ↔ FiniteType (overPullbackSnd f X.obj))

/- Lemma 70.19.2: proper morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.proper_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    Proper X.obj.hom ↔ Proper (overPullbackSnd f X.obj))

/- Lemma 70.19.2: integral morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.isIntegralHom_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    IsIntegralHom X.obj.hom ↔ IsIntegralHom (overPullbackSnd f X.obj))

/- Lemma 70.19.2: finite morphisms correspond under separated étale excision. -/
@[stacks 0BGZ] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.isFinite_hom_iff :
    ∀ {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)),
    IsFinite X.obj.hom ↔ IsFinite (overPullbackSnd f X.obj))
