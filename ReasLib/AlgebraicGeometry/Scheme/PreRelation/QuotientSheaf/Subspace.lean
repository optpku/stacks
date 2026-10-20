module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.InvariantImmersion
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality

/-!
# Locally closed subspaces of quotient sheaves

Pullback along the quotient atlas and quotienting the restricted relation give the
correspondence between locally closed subspaces and invariant locally closed subschemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- A locally closed subspace of `U / R` is an fppf sheaf over `S` with a relative immersion
into the quotient sheaf, with respect to `uliftYoneda`. -/
structure LocallyClosedSubspace {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] where
  /-- The fppf sheaf underlying the locally closed subspace. -/
  X : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  /-- The inclusion of the subspace into `U / R`. -/
  ι : X ⟶ P.quotientSheaf (Scheme.fppfTopology.over S)
  /-- The inclusion is a relative immersion with respect to `uliftYoneda`. -/
  isImmersion :
    (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} ι.hom

namespace LocallyClosedSubspace

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U} [P.IsEtaleEquivalenceRelation]

/-- The locally closed subspace determined by a relative immersion into the quotient sheaf. -/
def ofι {X : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (ι : X ⟶ P.quotientSheaf (Scheme.fppfTopology.over S))
    (immersion : (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} ι.hom) :
    LocallyClosedSubspace P where
  X := X
  ι := ι
  isImmersion := immersion

/-- A relative immersion of fppf sheaves is a monomorphism of underlying presheaves. -/
instance mono_hom (Z : LocallyClosedSubspace P) : Mono Z.ι.hom := sorry

/-- The inclusion of a locally closed subspace is a relative immersion and a monomorphism
of underlying presheaves. -/
theorem spec (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ∧
      Mono Z.ι.hom := sorry

/-- The subobject of the underlying quotient presheaf represented by a locally closed
subspace. -/
def subobject (Z : LocallyClosedSubspace P) :
    Subobject (P.quotientSheaf (Scheme.fppfTopology.over S)).obj :=
  Subobject.mk Z.ι.hom

/-- The subobject of a locally closed subspace is represented by its inclusion. -/
theorem subobject_eq_mk (Z : LocallyClosedSubspace P) :
    Z.subobject = @Subobject.mk _ _ _ _ Z.ι.hom (mono_hom Z) := sorry

/-- Two locally closed subspace presentations are equivalent when their subobjects agree. -/
def subobjectSetoid (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    Setoid (LocallyClosedSubspace P) where
  r first second := first.subobject = second.subobject
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun first second => first.trans second⟩

/-- Locally closed subspaces of the quotient, independent of their sheaf presentations. -/
def SubobjectClass (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :=
  Quotient (subobjectSetoid P)

/-- The invariant immersion obtained by pulling a subspace back along the quotient atlas. -/
def pullbackAlong (Z : LocallyClosedSubspace P) : InvariantImmersion P where
  Z := Z.isImmersion.rep.pullback (P.quotientMap (Scheme.fppfTopology.over S)).hom
  ι := Z.isImmersion.rep.snd (P.quotientMap (Scheme.fppfTopology.over S)).hom
  isImmersion := Z.isImmersion.property_snd (P.quotientMap (Scheme.fppfTopology.over S)).hom
  isInvariant := sorry

/-- The underlying scheme of the atlas pullback is the represented fibre product. -/
theorem pullbackAlong_Z (Z : LocallyClosedSubspace P) :
    (pullbackAlong Z).Z =
      Z.isImmersion.rep.pullback (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The inclusion of the atlas pullback is the represented pullback projection. -/
theorem pullbackAlong_ι (Z : LocallyClosedSubspace P) :
    (pullbackAlong Z).ι =
      Z.isImmersion.rep.snd (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- Atlas pullback sends equal subspace subobjects to equal subscheme subobjects. -/
theorem pullbackAlong_respects_subobject {first second : LocallyClosedSubspace P}
    (equality : first.subobject = second.subobject) :
    first.pullbackAlong.subobject = second.pullbackAlong.subobject := sorry

end LocallyClosedSubspace

namespace InvariantImmersion

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U} [P.IsEtaleEquivalenceRelation]

/-- The subspace obtained by quotienting the restriction of the relation to an invariant
immersion. -/
def toLocallyClosedSubspace (Z' : InvariantImmersion P) : LocallyClosedSubspace P where
  X := (P.pullback Z'.ι).quotientSheaf (Scheme.fppfTopology.over S)
  ι := (P.pullbackHom Z'.ι).quotientSheafMap (Scheme.fppfTopology.over S)
  isImmersion := sorry

/-- The underlying sheaf of the descended subspace is the quotient of the restricted relation. -/
theorem toLocallyClosedSubspace_X (Z' : InvariantImmersion P) :
    (toLocallyClosedSubspace Z').X =
      (P.pullback Z'.ι).quotientSheaf (Scheme.fppfTopology.over S) := sorry

/-- The descended inclusion is the map on quotient sheaves induced by restriction. -/
theorem toLocallyClosedSubspace_ι (Z' : InvariantImmersion P) :
    (toLocallyClosedSubspace Z').ι =
      (P.pullbackHom Z'.ι).quotientSheafMap (Scheme.fppfTopology.over S) := sorry

/-- The quotient of an invariant immersion is relatively closed if and only if the original
immersion is closed. -/
theorem isClosedImmersion_toLocallyClosedSubspace_iff (Z' : InvariantImmersion P) :
    (over (@AlgebraicGeometry.IsClosedImmersion)).relative uliftYoneda.{u + 1}
        (toLocallyClosedSubspace Z').ι.hom ↔
      AlgebraicGeometry.IsClosedImmersion Z'.ι.left := sorry

/-- The quotient of an invariant immersion is relatively open if and only if the original
immersion is open. -/
theorem isOpenImmersion_toLocallyClosedSubspace_iff (Z' : InvariantImmersion P) :
    (over (@AlgebraicGeometry.IsOpenImmersion)).relative uliftYoneda.{u + 1}
        (toLocallyClosedSubspace Z').ι.hom ↔
      AlgebraicGeometry.IsOpenImmersion Z'.ι.left := sorry

/-- Quotienting the restricted relation sends equal subscheme subobjects to equal subspace
subobjects. -/
theorem toLocallyClosedSubspace_respects_subobject {first second : InvariantImmersion P}
    (equality : first.subobject = second.subobject) :
    first.toLocallyClosedSubspace.subobject = second.toLocallyClosedSubspace.subobject := sorry

end InvariantImmersion

/-- Pulling a subspace back along the quotient atlas and quotienting the restricted relation
recovers the original subspace subobject. -/
theorem pullbackAlong_toLocallyClosedSubspace_subobject {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (Z.pullbackAlong.toLocallyClosedSubspace).subobject = Z.subobject := sorry

/-- Quotienting an invariant immersion and pulling the descended subspace back along the
quotient atlas recovers the original subscheme subobject. -/
theorem toLocallyClosedSubspace_pullbackAlong_subobject {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z' : InvariantImmersion P) :
    (Z'.toLocallyClosedSubspace.pullbackAlong).subobject = Z'.subobject := sorry

/-- A subspace inclusion is relatively closed if and only if its atlas pullback is closed. -/
theorem isClosedImmersion_pullbackAlong_iff {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsClosedImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsClosedImmersion Z.pullbackAlong.ι.left := sorry

/-- A subspace inclusion is relatively open if and only if its atlas pullback is open. -/
theorem isOpenImmersion_pullbackAlong_iff {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsOpenImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ↔
      AlgebraicGeometry.IsOpenImmersion Z.pullbackAlong.ι.left := sorry

/-- Invariant locally closed subschemes correspond to locally closed subspaces of the quotient
by descending the restricted relation, with inverse given by atlas pullback. -/
def locallyClosedSubspaceEquiv {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    InvariantImmersion.SubobjectClass P ≃ LocallyClosedSubspace.SubobjectClass P where
  toFun := Quotient.map InvariantImmersion.toLocallyClosedSubspace
    (fun {_ _} equality => InvariantImmersion.toLocallyClosedSubspace_respects_subobject equality)
  invFun := Quotient.map LocallyClosedSubspace.pullbackAlong
    (fun {_ _} equality => LocallyClosedSubspace.pullbackAlong_respects_subobject equality)
  left_inv := fun subscheme => Quotient.inductionOn subscheme fun representative =>
    Quotient.sound (toLocallyClosedSubspace_pullbackAlong_subobject P representative)
  right_inv := fun subspace => Quotient.inductionOn subspace fun representative =>
    Quotient.sound (pullbackAlong_toLocallyClosedSubspace_subobject P representative)

/-- The subspace correspondence sends an invariant immersion class to its restricted quotient
class. -/
theorem locallyClosedSubspaceEquiv_apply_mk {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] (Z' : InvariantImmersion P) :
    locallyClosedSubspaceEquiv P (Quotient.mk (InvariantImmersion.subobjectSetoid P) Z') =
      Quotient.mk (LocallyClosedSubspace.subobjectSetoid P) Z'.toLocallyClosedSubspace := rfl

/-- The inverse subspace correspondence sends a subspace class to its atlas pullback class. -/
theorem locallyClosedSubspaceEquiv_symm_apply_mk {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] (Z : LocallyClosedSubspace P) :
    (locallyClosedSubspaceEquiv P).symm (Quotient.mk (LocallyClosedSubspace.subobjectSetoid P) Z) =
      Quotient.mk (InvariantImmersion.subobjectSetoid P) Z.pullbackAlong := rfl

end AlgebraicGeometry.Scheme.PreRelation
