module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Subfunctor.Precomp
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of locally-ringed-space functors to schemes

This leaf records the canonical restriction along
`Scheme.forgetToLocallyRingedSpace`, including its objectwise computations and
the transfer of representations by a scheme.
-/

@[expose] public section

open AlgebraicGeometry Opposite

universe u v

namespace CategoryTheory.Functor

/-- The explicit data that a locally-ringed-space functor is represented by the underlying
locally ringed space of a specified scheme. -/
@[stacks 01JK "representation by a specified scheme"]
abbrev RepresentableByScheme (F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v)
    (X : Scheme.{u}) :=
  F.RepresentableBy X.toLocallyRingedSpace

/-- A contravariant set-valued functor on locally ringed spaces is represented by a scheme when
it has a representing object in the essential image of `Scheme.forgetToLocallyRingedSpace`. -/
@[stacks 01JK "representability by a scheme"]
def IsRepresentableByScheme (F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∃ X : Scheme.{u}, Nonempty (F.RepresentableByScheme X)

/-- In the hom-valued universe, a functor is represented by a scheme exactly when it is
isomorphic to the Yoneda functor of that scheme after viewing it as a locally ringed space. -/
@[stacks 01JK]
theorem isRepresentableByScheme_iff
    (F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type u) :
    F.IsRepresentableByScheme ↔
      ∃ X : Scheme.{u}, Nonempty (yoneda.obj X.toLocallyRingedSpace ≅ F) := sorry

/-- Restrict a contravariant set-valued functor on locally ringed spaces to schemes along the
canonical forgetful functor. -/
@[stacks 01JK "restriction to schemes"]
def onSchemes (F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v) : Scheme.{u}ᵒᵖ ⥤ Type v :=
  Scheme.forgetToLocallyRingedSpace.op ⋙ F

/-- A functor represented by a scheme restricts to a representable functor on schemes. -/
@[stacks 01JK]
theorem IsRepresentableByScheme.onSchemes_isRepresentable
    {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v}
    (hF : F.IsRepresentableByScheme) :
    F.onSchemes.IsRepresentable := sorry

namespace IsRepresentableByScheme

variable {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v}

/-- A chosen scheme representing a functor known to be representable by a scheme. -/
@[stacks 01JK "representing scheme"]
noncomputable def representingScheme (hF : F.IsRepresentableByScheme) : Scheme.{u} :=
  hF.choose

/-- The explicit representation carried by `representingScheme`. -/
@[stacks 01JK "representation carried by the representing scheme"]
noncomputable def representableBy (hF : F.IsRepresentableByScheme) :
    F.RepresentableByScheme hF.representingScheme :=
  hF.choose_spec.some

/-- The chosen representing scheme satisfies the defining representation property. -/
@[stacks 01JK]
theorem representingScheme_spec (hF : F.IsRepresentableByScheme) :
    Nonempty (F.RepresentableByScheme hF.representingScheme) := sorry

/-- The chosen representing scheme is independent of the proof of scheme representability. -/
@[stacks 01JK "proof independence of the representing scheme"]
theorem representingScheme_eq (hF hF' : F.IsRepresentableByScheme) :
    hF.representingScheme = hF'.representingScheme := sorry

/-- In the hom-valued universe, the representation is the usual Yoneda isomorphism. -/
@[stacks 01JK "Yoneda isomorphism of a representing scheme"]
noncomputable abbrev yonedaIso
    {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type u}
    (hF : F.IsRepresentableByScheme) :
    yoneda.obj hF.representingScheme.toLocallyRingedSpace ≅ F :=
  hF.representableBy.toIso

/-- The chosen representing scheme is canonically isomorphic to any other scheme carrying a
representation of the same functor. -/
@[stacks 01JK "uniqueness isomorphism of representing schemes"]
noncomputable def representingIso (hF : F.IsRepresentableByScheme) {X : Scheme.{u}}
    (hX : F.RepresentableByScheme X) : hF.representingScheme ≅ X :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (hF.representableBy.uniqueUpToIso hX)

/-- After forgetting to locally ringed spaces, `representingIso` is the canonical uniqueness
isomorphism between the two representations. -/
@[stacks 01JK]
theorem map_representingIso (hF : F.IsRepresentableByScheme) {X : Scheme.{u}}
    (hX : F.RepresentableByScheme X) :
    Scheme.forgetToLocallyRingedSpace.mapIso (hF.representingIso hX) =
      hF.representableBy.uniqueUpToIso hX := sorry

/-- A locally-ringed-space functor represented by a scheme is representable in the ambient
category of locally ringed spaces. -/
@[stacks 01JK]
theorem isRepresentable (hF : F.IsRepresentableByScheme) :
    F.IsRepresentable := sorry

end IsRepresentableByScheme

namespace RepresentableByScheme

variable {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v} {X : Scheme.{u}}

/-- Restrict a fixed representation by a scheme along the fully faithful forgetful functor. -/
@[stacks 01JK "representation data restricted to schemes"]
noncomputable def onSchemes (R : F.RepresentableByScheme X) :
    F.onSchemes.RepresentableBy X where
  homEquiv {T} :=
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.homEquiv.trans R.homEquiv
  homEquiv_comp := sorry

/-- The scheme-side representation uses the underlying locally-ringed-space morphism. -/
@[stacks 01JK "scheme-side representation computation"]
theorem onSchemes_homEquiv (R : F.RepresentableByScheme X)
    {T : Scheme.{u}} (f : T ⟶ X) :
    R.onSchemes.homEquiv f =
      R.homEquiv (Scheme.forgetToLocallyRingedSpace.map f) := sorry

end RepresentableByScheme

end CategoryTheory.Functor

namespace CategoryTheory.Subfunctor

open AlgebraicGeometry

/-- A subfunctor is represented by a scheme when its associated set-valued functor is represented
by a scheme. -/
@[stacks 01JK "subfunctor representability by a scheme"]
def IsRepresentableByScheme {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v}
    (H : Subfunctor F) : Prop :=
  H.toFunctor.IsRepresentableByScheme

/-- Restrict a subfunctor on locally ringed spaces to schemes along
`Scheme.forgetToLocallyRingedSpace`. -/
@[stacks 01JK "restriction of a subfunctor to schemes"]
abbrev onSchemes {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v} (H : Subfunctor F) :
    Subfunctor F.onSchemes :=
  H.precomp Scheme.forgetToLocallyRingedSpace.op

/-- A subfunctor represented by a scheme restricts to a representable scheme-side subfunctor. -/
@[stacks 01JK]
theorem IsRepresentableByScheme.onSchemes_isRepresentable
    {F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v} {H : Subfunctor F}
    (hH : H.IsRepresentableByScheme) :
    H.onSchemes.toFunctor.IsRepresentable := sorry

end CategoryTheory.Subfunctor
