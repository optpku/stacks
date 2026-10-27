/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.Excision
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-! # Morphism properties under separated étale excision -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsoOverOpen

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is quasi-compact if and only if its
base change is quasi-compact. -/
@[stacks 0BGZ]
theorem quasiCompact_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    QuasiCompact X.obj.hom ↔ QuasiCompact (overPullbackSnd f X.obj) :=
  sorry

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is quasi-separated if and only if its
base change is quasi-separated. -/
@[stacks 0BGZ]
theorem quasiSeparated_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    QuasiSeparated X.obj.hom ↔ QuasiSeparated (overPullbackSnd f X.obj) :=
  sorry

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is separated if and only if its
base change is separated. -/
@[stacks 0BGZ]
theorem separated_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    Separated X.obj.hom ↔ Separated (overPullbackSnd f X.obj) :=
  sorry

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is locally of finite presentation if and only if its
base change is locally of finite presentation. -/
@[stacks 0BGZ]
theorem locallyOfFinitePresentation_hom_iff {S : Scheme.{u}}
    {V W T : AlgebraicSpace S} (f : V ⟶ W) [Etale f] [Separated f]
    (i : T ⟶ W) [IsClosedImmersion i] [IsIso (inverseImageTo f i)]
    (X : IsoOverOpen (closedImmersionComplementι i)) :
    LocallyOfFinitePresentation X.obj.hom ↔
      LocallyOfFinitePresentation (overPullbackSnd f X.obj) :=
  sorry

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is of finite presentation if and only if its
base change is of finite presentation. -/
@[stacks 0BGZ]
theorem finitePresentation_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    FinitePresentation X.obj.hom ↔ FinitePresentation (overPullbackSnd f X.obj) := by
  constructor
  · intro h
    letI := h
    exact
      { toLocallyOfFinitePresentation :=
          (locallyOfFinitePresentation_hom_iff f i X).mp inferInstance
        toQuasiCompact := (quasiCompact_hom_iff f i X).mp inferInstance
        toQuasiSeparated := (quasiSeparated_hom_iff f i X).mp inferInstance }
  · intro h
    letI := h
    exact
      { toLocallyOfFinitePresentation :=
          (locallyOfFinitePresentation_hom_iff f i X).mpr inferInstance
        toQuasiCompact := (quasiCompact_hom_iff f i X).mpr inferInstance
        toQuasiSeparated := (quasiSeparated_hom_iff f i X).mpr inferInstance }

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is locally of finite type if and only if its
base change is locally of finite type. -/
@[stacks 0BGZ]
theorem locallyOfFiniteType_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    LocallyOfFiniteType X.obj.hom ↔ LocallyOfFiniteType (overPullbackSnd f X.obj) :=
  sorry

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is of finite type if and only if its
base change is of finite type. -/
@[stacks 0BGZ]
theorem finiteType_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    FiniteType X.obj.hom ↔ FiniteType (overPullbackSnd f X.obj) := by
  constructor
  · intro h
    letI := h
    exact
      { toQuasiCompact := (quasiCompact_hom_iff f i X).mp inferInstance
        toLocallyOfFiniteType := (locallyOfFiniteType_hom_iff f i X).mp inferInstance }
  · intro h
    letI := h
    exact
      { toQuasiCompact := (quasiCompact_hom_iff f i X).mpr inferInstance
        toLocallyOfFiniteType := (locallyOfFiniteType_hom_iff f i X).mpr inferInstance }

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is proper if and only if its
base change is proper. -/
@[stacks 0BGZ]
theorem proper_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    Proper X.obj.hom ↔ Proper (overPullbackSnd f X.obj) :=
  sorry

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is integral if and only if its
base change is integral. -/
@[stacks 0BGZ]
theorem isIntegralHom_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    IsIntegralHom X.obj.hom ↔ IsIntegralHom (overPullbackSnd f X.obj) :=
  sorry

/-- Under separated étale excision along a closed subspace, a morphism that is an
isomorphism over the complementary open is finite if and only if its
base change is finite. -/
@[stacks 0BGZ]
theorem isFinite_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    IsFinite X.obj.hom ↔ IsFinite (overPullbackSnd f X.obj) :=
  sorry

end IsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
