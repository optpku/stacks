module

public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.ResidueField
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prime localizations of over-objects

An object over a fixed target determines a prime through the kernel of its
target map.  This leaf owns the resulting maps between prime localizations,
their maximal-ideal and residue-field compatibility, and the named relative
algebra structure.  It has no etaleness hypothesis.

@stack 04GV
-/

open CategoryTheory

universe u v

namespace CommAlgCat.Over.Target.Localization

variable {R : Type u} {T : Type v} [CommRing R] [CommRing T] [IsDomain T] [Algebra R T]
variable {p : Ideal R} [p.IsPrime]

/-- The prime-localization map attached to an explicit contraction equality. -/
@[stacks 04GV "prime-localization map from an over-object"]
noncomputable abbrev mapOfComap
    (A : CategoryTheory.Over (CommAlgCat.of R T))
    (hA : p = Ideal.comap (algebraMap R A.left) (CommAlgCat.Over.Target.kernel A)) :
    _root_.Localization.AtPrime p →+*
      _root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A) :=
  _root_.Localization.localRingHom p (CommAlgCat.Over.Target.kernel A)
    (algebraMap R A.left) hA

/-- The canonical map from the base prime localization to the localization at
the target kernel. -/
@[stacks 04GV "canonical prime-localization map from an over-object"]
noncomputable abbrev map
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    _root_.Localization.AtPrime p →+*
      _root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A) :=
  mapOfComap A (CommAlgCat.Over.Target.baseComap hbase A)

/-- The canonical localization map contracts the selected maximal ideal to the
maximal ideal of the base localization. -/
@[stacks 04GV "maximal-ideal contraction for an over-object localization map"]
theorem map_comap_maximalIdeal
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    Ideal.comap (map hbase A)
        (IsLocalRing.maximalIdeal
          (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A))) =
      IsLocalRing.maximalIdeal (_root_.Localization.AtPrime p) := sorry

/-- The named algebra structure induced by the canonical localization map.
It is not global because distinct target maps can induce competing structures
on the same localization. -/
@[stacks 04GV "relative prime-localization algebra of an over-object"]
noncomputable abbrev algebra
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    Algebra (_root_.Localization.AtPrime p)
      (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A)) :=
  RingHom.toAlgebra (map hbase A)

/-- The localization map induced by a morphism of over-objects. -/
@[stacks 04GV "localized transition map of an over-object morphism"]
noncomputable abbrev hom
    {A B : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) :
    _root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A) →+*
      _root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel B) :=
  _root_.Localization.localRingHom
    (CommAlgCat.Over.Target.kernel A) (CommAlgCat.Over.Target.kernel B)
    (CommAlgCat.Over.Target.hom f) (CommAlgCat.Over.Target.kernel_comap f)

/-- A localized over-object morphism contracts the target maximal ideal to
the maximal ideal of its source. -/
@[stacks 04GV "maximal-ideal contraction for localized over-object morphisms"]
theorem hom_comap_maximalIdeal
    {A B : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) :
    Ideal.comap (hom f)
        (IsLocalRing.maximalIdeal
          (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel B))) =
      IsLocalRing.maximalIdeal
        (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A)) := sorry

/-- A localized over-object morphism commutes with the canonical map from the
base prime localization. -/
@[stacks 04GV "localized over-object map compatibility"]
theorem hom_comp_map
    (hbase : RingHom.ker (algebraMap R T) = p)
    {A B : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) :
    (hom f).comp (map hbase A) = map hbase B := sorry

/-- The localized map induced by an identity over-object morphism is the identity. -/
@[stacks 04GV "identity law for over-object localization"]
theorem hom_id {A : CategoryTheory.Over (CommAlgCat.of R T)} :
    hom (𝟙 A) = RingHom.id _ := sorry

/-- The localized map of a composite over-object morphism is the composite of
the localized maps. -/
@[stacks 04GV "composition law for over-object localization"]
theorem hom_comp {A B C : CategoryTheory.Over (CommAlgCat.of R T)}
    (f : A ⟶ B) (g : B ⟶ C) :
    hom (f ≫ g) = (hom g).comp (hom f) := sorry

/-! ### Bundled localized algebras -/

/-- The localized algebra object attached to an arbitrary over-object.  The
relative scalar structure is installed only while forming this bundled object,
because different target maps can induce competing structures on the same
localization. -/
@[stacks 04GV "localized over-object algebra"]
noncomputable abbrev object
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    CommAlgCat (_root_.Localization.AtPrime p) :=
  letI : Algebra (_root_.Localization.AtPrime p)
      (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A)) :=
    algebra hbase A
  CommAlgCat.of (_root_.Localization.AtPrime p)
    (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A))

/-- The bundled localized algebra morphism induced by an over-object morphism. -/
@[stacks 04GV "localized over-object algebra morphism"]
noncomputable def morphism
    (hbase : RingHom.ker (algebraMap R T) = p)
    {A B : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) :
    object hbase A ⟶ object hbase B :=
  letI : Algebra (_root_.Localization.AtPrime p)
      (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A)) :=
    algebra hbase A
  letI : Algebra (_root_.Localization.AtPrime p)
      (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel B)) :=
    algebra hbase B
  CommAlgCat.ofHom {
    toRingHom := hom f
    commutes' := fun r => DFunLike.congr_fun (hom_comp_map hbase f) r }

/-- The bundled localization of an identity over-object morphism is the
identity. -/
@[stacks 04GV "identity law for localized over-object algebra morphisms"]
theorem morphism_id
    (hbase : RingHom.ker (algebraMap R T) = p)
    {A : CategoryTheory.Over (CommAlgCat.of R T)} :
    morphism hbase (𝟙 A) = 𝟙 (object hbase A) := sorry

/-- The bundled localization of over-object morphisms respects composition. -/
@[stacks 04GV "composition law for localized over-object algebra morphisms"]
theorem morphism_comp
    (hbase : RingHom.ker (algebraMap R T) = p)
    {A B C : CategoryTheory.Over (CommAlgCat.of R T)} (f : A ⟶ B) (g : B ⟶ C) :
    morphism hbase (f ≫ g) = morphism hbase f ≫ morphism hbase g := sorry

/-- The underlying ring map of a localized over-object morphism to an arbitrary
chosen algebra over the base localization. -/
@[stacks 04GV "underlying map of a localized over-object morphism"]
noncomputable def ringHom
    {S : Type v} [CommRing S] [Algebra (_root_.Localization.AtPrime p) S]
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T))
    (f : object hbase A ⟶ CommAlgCat.of (_root_.Localization.AtPrime p) S) :
    _root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A) →+* S :=
  letI : Algebra (_root_.Localization.AtPrime p)
      (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A)) :=
    algebra hbase A
  f.hom.toRingHom

/-- The shared localized bridge forgets only the bundled commutative-algebra
structure. -/
@[stacks 04GV "underlying map specification for a localized over-object morphism"]
theorem ringHom_spec
    {S : Type v} [CommRing S] [Algebra (_root_.Localization.AtPrime p) S]
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T))
    (f : object hbase A ⟶ CommAlgCat.of (_root_.Localization.AtPrime p) S) :
    letI : Algebra (_root_.Localization.AtPrime p)
        (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A)) :=
      algebra hbase A
    ringHom hbase A f = f.hom.toRingHom := sorry

/-- The functor sending an over-object to the localization at the kernel of
its target map. -/
@[stacks 04GV "localized over-object functor"]
noncomputable def functor
    (hbase : RingHom.ker (algebraMap R T) = p) :
    CategoryTheory.Over (CommAlgCat.of R T) ⥤
      CommAlgCat (_root_.Localization.AtPrime p) where
  obj A := object hbase A
  map f := morphism hbase f
  map_id _ := morphism_id hbase
  map_comp f g := morphism_comp hbase f g

section ResidueField

variable {K : Type v} [Field K] [Algebra R K]

/-- The target map of the localization at an over-object kernel, factored
through its maximal-ideal residue field. -/
@[stacks 04GW "target residue map of an over-object localization"]
noncomputable abbrev residueFieldMap
    (A : CategoryTheory.Over (CommAlgCat.of R K)) :
    (IsLocalRing.maximalIdeal
      (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A))).ResidueField →+* K :=
  (CommAlgCat.Over.Target.ResidueField.map A).comp
    (IsLocalRing.ResidueField.maximalIdealAlgEquiv
      (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A))).symm.toRingHom

/-- The target map of the base prime localization, factored through its
maximal-ideal residue field. -/
@[stacks 04GW "base residue map of an over-object localization"]
noncomputable abbrev baseResidueFieldMap
    (hbase : RingHom.ker (algebraMap R K) = p) :
    (IsLocalRing.maximalIdeal (_root_.Localization.AtPrime p)).ResidueField →+* K :=
    (CommAlgCat.Over.Target.ResidueField.baseMap hbase).comp
    (IsLocalRing.ResidueField.maximalIdealAlgEquiv
      (_root_.Localization.AtPrime p)).symm.toRingHom

/-! The ordinary-residue-field form is the one consumed by generic strict
henselization coordinates.  Keeping this bridge here makes the choice of
residue presentation explicit at the target-localization boundary. -/

/-- The base residue map on the ordinary residue field of `Rₚ`. -/
@[stacks 04GW "ordinary base residue map at a prime localization"]
noncomputable abbrev baseResidueMap
    (hbase : RingHom.ker (algebraMap R K) = p) :
    IsLocalRing.ResidueField (_root_.Localization.AtPrime p) →+* K :=
  (baseResidueFieldMap hbase).comp
    (IsLocalRing.ResidueField.maximalIdealAlgEquiv
      (_root_.Localization.AtPrime p)).toRingHom

/-! The ordinary-residue-field form is useful when a target coordinate is
specified on `IsLocalRing.ResidueField` rather than on the maximal-ideal
presentation. -/

/-- The ordinary residue map of the base localization is the direct
target-residue factorization through `p.ResidueField`. -/
@[stacks 04GW "ordinary residue form of the base localized residue map"]
theorem baseResidueMap_eq_baseMap
    (hbase : RingHom.ker (algebraMap R K) = p) :
    baseResidueMap hbase =
      CommAlgCat.Over.Target.ResidueField.baseMap hbase := sorry

/-- The two localized target residue maps commute with the residue-field map
induced by the canonical localization map. -/
@[stacks 04GW "localized target residue-map compatibility"]
theorem residueFieldMap_comp_base
    (hbase : RingHom.ker (algebraMap R K) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R K)) :
    (residueFieldMap A).comp
        (Ideal.ResidueField.map
          (IsLocalRing.maximalIdeal (_root_.Localization.AtPrime p))
          (IsLocalRing.maximalIdeal
            (_root_.Localization.AtPrime (CommAlgCat.Over.Target.kernel A)))
          (map hbase A) (map_comap_maximalIdeal hbase A).symm) =
      baseResidueFieldMap hbase := sorry

end ResidueField

end CommAlgCat.Over.Target.Localization
