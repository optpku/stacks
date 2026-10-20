module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen

/-!
# Base change for finite-presentation morphisms that are isomorphisms over an open

This leaf separates the elementary stability of an isomorphism after open
restriction from approximation-specific arguments. In particular, base change
along an arbitrary scheme morphism preserves being an isomorphism over the
inverse-image open; the base-change morphism itself need not be an isomorphism
there. It exposes both proposition-valued stability statements and the induced
functors between the corresponding full subcategories. The canonical raw
base-change functor remains `Over.pullback`; the lifted functors retain its
object and morphism computations through named API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- If a scheme morphism is an isomorphism over `U`, then it is an isomorphism over every
smaller open `V ≤ U`. -/
theorem isIso_restrict_of_le
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Opens}
    (hVU : V ≤ U) (h : IsIso (f ∣_ U)) :
    IsIso (f ∣_ V) := sorry

/-- Base changing a scheme morphism that is an isomorphism over `U` yields a morphism that is
an isomorphism over the inverse-image open `s ⁻¹ᵁ U`. -/
theorem isIso_restrict_pullback_snd
    {X S W : Scheme.{u}} (f : X ⟶ S) (s : W ⟶ S) (U : S.Opens)
    (h : IsIso (f ∣_ U)) :
    IsIso (pullback.snd f s ∣_ (s ⁻¹ᵁ U)) := sorry

/-- The base change of a morphism that is an isomorphism over `U` is an isomorphism after
restriction to any open `V` contained in `s ⁻¹ᵁ U`. -/
theorem isIso_restrict_pullback_snd_of_le
    {X S W : Scheme.{u}} (f : X ⟶ S) (s : W ⟶ S) (U : S.Opens)
    {V : W.Opens} (hV : V ≤ s ⁻¹ᵁ U) (h : IsIso (f ∣_ U)) :
    IsIso (pullback.snd f s ∣_ V) := sorry

/-- The isomorphism-over-open property is available to typeclass search after arbitrary base
change. -/
instance instIsIsoRestrictPullbackSnd
    {X S W : Scheme.{u}} (f : X ⟶ S) (s : W ⟶ S) (U : S.Opens)
    [IsIso (f ∣_ U)] :
    IsIso (pullback.snd f s ∣_ (s ⁻¹ᵁ U)) := sorry

/-- The finite-presentation/isomorphism-over-open condition is stable on passing to a smaller
open subset of the target. -/
theorem isFinitePresentationIsoOverOpen_restrict_of_le
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Opens}
    (hVU : V ≤ U) (h : f.IsFinitePresentationIsoOverOpen U) :
    f.IsFinitePresentationIsoOverOpen V := sorry

/-- The finite-presentation/isomorphism-over-open condition is stable under arbitrary base
change, with target open given by inverse image. -/
theorem isFinitePresentationIsoOverOpen_pullback_snd
    {X S W : Scheme.{u}} (f : X ⟶ S) (s : W ⟶ S) (U : S.Opens)
    (h : f.IsFinitePresentationIsoOverOpen U) :
    (pullback.snd f s).IsFinitePresentationIsoOverOpen (s ⁻¹ᵁ U) := sorry

/-- After arbitrary base change, the finite-presentation/isomorphism-over-open condition holds
over every open `V` contained in the inverse image of `U`. -/
theorem isFinitePresentationIsoOverOpen_pullback_snd_of_le
    {X S W : Scheme.{u}} (f : X ⟶ S) (s : W ⟶ S) (U : S.Opens)
    {V : W.Opens} (hV : V ≤ s ⁻¹ᵁ U)
    (h : f.IsFinitePresentationIsoOverOpen U) :
    (pullback.snd f s).IsFinitePresentationIsoOverOpen V := sorry

end Scheme.Hom

namespace FinitePresentationIsoOverOpen

/-- Arbitrary base change preserves the finite-presentation/isomorphism-over-open property. -/
theorem baseChange_mem
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    (X : FinitePresentationIsoOverOpen U) :
    finitePresentationIsoOverOpenProperty (s ⁻¹ᵁ U) ((Over.pullback s).obj X.obj) := sorry

/-- Base change along an arbitrary scheme morphism on finite-presentation morphisms that are
isomorphisms over the designated open. Its underlying slice functor is `Over.pullback s`; the
full-subcategory proof field is supplied by `baseChange_mem`. -/
noncomputable def baseChange
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens) :
    FinitePresentationIsoOverOpen U ⥤ FinitePresentationIsoOverOpen (s ⁻¹ᵁ U) :=
  ObjectProperty.lift
    (finitePresentationIsoOverOpenProperty (s ⁻¹ᵁ U))
    ((inclusion U) ⋙ Over.pullback s)
    (fun X ↦ baseChange_mem s U X)

/-- After forgetting the isomorphism-over-open property, `baseChange` is the ordinary slice
base-change functor. -/
noncomputable def baseChangeInclusionIso
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens) :
    baseChange s U ⋙ inclusion (s ⁻¹ᵁ U) ≅ inclusion U ⋙ Over.pullback s :=
  (finitePresentationIsoOverOpenProperty (s ⁻¹ᵁ U)).liftCompιIso
    ((inclusion U) ⋙ Over.pullback s)
    (fun X ↦ baseChange_mem s U X)

/-- The structural morphism of a `baseChange` object is the usual pullback second projection. -/
theorem baseChange_obj_hom
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    (X : FinitePresentationIsoOverOpen U) :
    ((baseChange s U).obj X).obj.hom = pullback.snd X.obj.hom s := sorry

/-- On morphisms, `baseChange` is the ordinary slice base-change functor after forgetting the
open-isomorphism condition. -/
theorem baseChange_map_hom
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    {X Y : FinitePresentationIsoOverOpen U} (f : X ⟶ Y) :
    ((baseChange s U).map f).hom = (Over.pullback s).map f.hom := sorry

/-- A finite-presentation morphism that is an isomorphism over `U` is also one over every
smaller open `V ≤ U`. -/
theorem restrict_mem
    {S : Scheme.{u}} (U V : S.Opens) (hVU : V ≤ U)
    (X : FinitePresentationIsoOverOpen U) :
    finitePresentationIsoOverOpenProperty V X.obj := sorry

/-- Forgetting part of the open set gives a functor between the corresponding
finite-presentation/isomorphism-over-open subcategories. -/
noncomputable def restrict
    {S : Scheme.{u}} (U V : S.Opens) (hVU : V ≤ U) :
    FinitePresentationIsoOverOpen U ⥤ FinitePresentationIsoOverOpen V :=
  ObjectProperty.lift
    (finitePresentationIsoOverOpenProperty V)
    (inclusion U)
    (fun X ↦ restrict_mem U V hVU X)

/-- After inclusion into `Over S`, `restrict` is the identity on the underlying slice objects. -/
noncomputable def restrictInclusionIso
    {S : Scheme.{u}} (U V : S.Opens) (hVU : V ≤ U) :
    restrict U V hVU ⋙ inclusion V ≅ inclusion U :=
  (finitePresentationIsoOverOpenProperty V).liftCompιIso
    (inclusion U)
    (fun X ↦ restrict_mem U V hVU X)

/-- Arbitrary base change followed by restriction to `V ≤ s ⁻¹ᵁ U` preserves the
finite-presentation/isomorphism-over-open property. -/
theorem baseChangeRestrict_mem
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    {V : W.Opens} (hV : V ≤ s ⁻¹ᵁ U)
    (X : FinitePresentationIsoOverOpen U) :
    finitePresentationIsoOverOpenProperty V ((Over.pullback s).obj X.obj) := sorry

/-- Base change of finite-presentation morphisms that are isomorphisms over `U`, with the
target property restricted to an arbitrary open `V ≤ s ⁻¹ᵁ U`. -/
noncomputable def baseChangeRestrict
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    {V : W.Opens} (hV : V ≤ s ⁻¹ᵁ U) :
    FinitePresentationIsoOverOpen U ⥤ FinitePresentationIsoOverOpen V :=
  ObjectProperty.lift
    (finitePresentationIsoOverOpenProperty V)
    ((inclusion U) ⋙ Over.pullback s)
    (fun X ↦ baseChangeRestrict_mem s U hV X)

/-- After forgetting the target open condition, `baseChangeRestrict` is ordinary slice base
change. -/
noncomputable def baseChangeRestrictInclusionIso
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    {V : W.Opens} (hV : V ≤ s ⁻¹ᵁ U) :
    baseChangeRestrict s U hV ⋙ inclusion V ≅ inclusion U ⋙ Over.pullback s :=
  (finitePresentationIsoOverOpenProperty V).liftCompιIso
    ((inclusion U) ⋙ Over.pullback s)
    (fun X ↦ baseChangeRestrict_mem s U hV X)

/-- The structural morphism of a `baseChangeRestrict` object is the usual pullback second
projection. -/
theorem baseChangeRestrict_obj_hom
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    {V : W.Opens} (hV : V ≤ s ⁻¹ᵁ U)
    (X : FinitePresentationIsoOverOpen U) :
    ((baseChangeRestrict s U hV).obj X).obj.hom = pullback.snd X.obj.hom s := sorry

/-- On morphisms, `baseChangeRestrict` is ordinary slice base change after the target open
condition is forgotten. -/
theorem baseChangeRestrict_map_hom
    {S W : Scheme.{u}} (s : W ⟶ S) (U : S.Opens)
    {V : W.Opens} (hV : V ≤ s ⁻¹ᵁ U)
    {X Y : FinitePresentationIsoOverOpen U} (f : X ⟶ Y) :
    ((baseChangeRestrict s U hV).map f).hom = (Over.pullback s).map f.hom := sorry

end FinitePresentationIsoOverOpen

end AlgebraicGeometry
