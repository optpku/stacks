module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap70.Lemma_70_19_1

/-!
# Transport of morphism properties across excision for modifications

Under the correspondence of Lemma 70.19.1, a morphism `g : X ⟶ W` that is an
isomorphism over the complementary open of `i` is quasi-compact, quasi-separated,
separated, locally of finite presentation, of finite presentation, locally of
finite type, of finite type, proper, integral, or finite if and only if the
corresponding morphism `h : Y ⟶ V` is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsoOverOpen

/-- Lemma 70.19.2 (1): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is
quasi-compact if and only if `h` is. -/
@[stacks 0BGZ]
theorem quasiCompact_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    QuasiCompact X.obj.hom ↔ QuasiCompact (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (2): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is
quasi-separated if and only if `h` is. -/
@[stacks 0BGZ]
theorem quasiSeparated_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    QuasiSeparated X.obj.hom ↔ QuasiSeparated (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (3): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is
separated if and only if `h` is. -/
@[stacks 0BGZ]
theorem separated_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    Separated X.obj.hom ↔ Separated (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (4): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is locally
of finite presentation if and only if `h` is. -/
@[stacks 0BGZ]
theorem locallyOfFinitePresentation_hom_iff {S : Scheme.{u}}
    {V W T : AlgebraicSpace S} (f : V ⟶ W) [Etale f] [Separated f]
    (i : T ⟶ W) [IsClosedImmersion i] [IsIso (inverseImageTo f i)]
    (X : IsoOverOpen (closedImmersionComplementι i)) :
    LocallyOfFinitePresentation X.obj.hom ↔
      LocallyOfFinitePresentation (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (5): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is of
finite presentation if and only if `h` is. -/
@[stacks 0BGZ]
theorem finitePresentation_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    FinitePresentation X.obj.hom ↔ FinitePresentation (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (6): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is locally
of finite type if and only if `h` is. -/
@[stacks 0BGZ]
theorem locallyOfFiniteType_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    LocallyOfFiniteType X.obj.hom ↔ LocallyOfFiniteType (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (7): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is of
finite type if and only if `h` is. -/
@[stacks 0BGZ]
theorem finiteType_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    FiniteType X.obj.hom ↔ FiniteType (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (8): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is proper
if and only if `h` is. -/
@[stacks 0BGZ]
theorem proper_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    Proper X.obj.hom ↔ Proper (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (9): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is integral
if and only if `h` is. -/
@[stacks 0BGZ]
theorem isIntegralHom_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    IsIntegralHom X.obj.hom ↔ IsIntegralHom (overPullbackSnd f X.obj) :=
  sorry

/-- Lemma 70.19.2 (10): under the assumptions of Lemma 70.19.1, if `g : X ⟶ W`
corresponds to `h : Y ⟶ V` via `IsoOverOpen.baseChange`, then `g` is finite
if and only if `h` is. -/
@[stacks 0BGZ]
theorem isFinite_hom_iff {S : Scheme.{u}} {V W T : AlgebraicSpace S}
    (f : V ⟶ W) [Etale f] [Separated f] (i : T ⟶ W) [IsClosedImmersion i]
    [IsIso (inverseImageTo f i)] (X : IsoOverOpen (closedImmersionComplementι i)) :
    IsFinite X.obj.hom ↔ IsFinite (overPullbackSnd f X.obj) :=
  sorry

end IsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
