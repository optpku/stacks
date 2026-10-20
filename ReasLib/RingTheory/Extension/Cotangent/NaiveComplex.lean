module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naive Cotangent Complexes of Algebra Presentations

@stack 07BN

This leaf owns the two-term chain-complex model attached to an algebra
presentation, its functorial chain maps, and the presentation-independence
homotopy data.  It is independent of any textbook chapter or chosen class of
presentations.
-/

open CategoryTheory
open CategoryTheory.Limits

universe u v w x

noncomputable section

namespace Algebra.Extension.NaiveCotangent

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The degree-one module of the naive cotangent complex, represented by a
universe lift of the conormal module of a presentation. -/
abbrev Lift (P : Extension.{w} R S) :=
  ULift.{v, w} P.Cotangent

/-- The canonical linear equivalence from the lifted conormal module to the
conormal module itself. -/
noncomputable abbrev liftEquiv (P : Extension.{w} R S) :
    Lift P ≃ₗ[S] P.Cotangent :=
  ULift.moduleEquiv

/-- A map from a presentation's cotangent space into its lifted conormal module.  This is the
degree-lowering datum used by contracting homotopies of naive cotangent complexes. -/
noncomputable def liftCotangentSpaceMap
    (P : Extension.{w} R S) (f : P.CotangentSpace →ₗ[S] P.Cotangent) :
    P.CotangentSpace →ₗ[S] Lift P :=
  (liftEquiv P).symm.toLinearMap ∘ₗ f

section Map

variable {R' : Type x} [CommRing R'] [Algebra R' S]
variable [Algebra R R'] [IsScalarTower R R' S]

/-- The map between lifted conormal modules induced by a morphism of algebra
presentations. -/
noncomputable def liftMap
    {P : Extension.{w} R S} {Q : Extension.{w} R' S} (f : P.Hom Q) :
    Lift P →ₗ[S] Lift Q :=
  (liftEquiv Q).symm.toLinearMap ∘ₗ Cotangent.map f ∘ₗ (liftEquiv P).toLinearMap

end Map

/-- The lifted conormal map of an identity presentation morphism is the
identity. -/
theorem liftMap_id (P : Extension.{w} R S) :
    liftMap (.id P) = LinearMap.id := sorry

/-- Lifted conormal maps respect composition of presentation morphisms. -/
theorem liftMap_comp
    {P Q T : Extension.{w} R S} (f : P.Hom Q) (g : Q.Hom T) :
    liftMap (g.comp f) = (liftMap g).restrictScalars S ∘ₗ liftMap f := sorry

/-- The degree-shifting map used to homotope chain maps arising from two
presentation morphisms. -/
noncomputable def liftHomotopyMap
    {P Q : Extension.{w} R S} (f g : P.Hom Q) :
    P.CotangentSpace →ₗ[S] Lift Q :=
  (liftEquiv Q).symm.toLinearMap ∘ₗ f.sub g

/-- The two-term naive cotangent chain complex of an algebra presentation has
degree-one term `Lift P`, degree-zero term `P.CotangentSpace`, and differential
given by the canonical cotangent map. -/
@[stacks 07BN "naive cotangent complex of an algebra presentation"]
noncomputable def complex (P : Extension.{w} R S) :
    ChainComplex (ModuleCat.{max v w} S) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of.{max v w} S P.CotangentSpace)
    (ModuleCat.of.{max v w} S (Lift P))
    (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftEquiv P).toLinearMap))
    (fun {_ _} _ => ⟨ModuleCat.of.{max v w} S PUnit, 0, CategoryTheory.Limits.zero_comp⟩)

/-- The degree-zero component of the naive cotangent complex is the cotangent
space of the presentation. -/
noncomputable def componentZeroIso (P : Extension.{w} R S) :
    (complex P).X 0 ≅ ModuleCat.of.{max v w} S P.CotangentSpace :=
  Iso.refl _

/-- The degree-one component of the naive cotangent complex is the lifted
conormal module of the presentation. -/
noncomputable def componentOneIso (P : Extension.{w} R S) :
    (complex P).X 1 ≅ ModuleCat.of.{max v w} S (Lift P) :=
  Iso.refl _

/-- The differential of the naive cotangent complex in degrees `1 → 0`. -/
@[simp]
theorem complex_d_one_zero (P : Extension.{w} R S) :
    (complex P).d 1 0 =
      ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftEquiv P).toLinearMap) := sorry

/-- All differentials of the naive cotangent complex above degree one vanish. -/
@[simp]
theorem complex_d_succ_succ (P : Extension.{w} R S) (n : ℕ) :
    (complex P).d (n + 2) (n + 1) = 0 := sorry

/-- The components of the naive cotangent complex in degrees at least two are
canonically the zero `S`-module. -/
noncomputable def componentSuccSuccIsoUnit
    (P : Extension.{w} R S) (i : ℕ) :
    (complex P).X (i + 2) ≅ ModuleCat.of.{max v w} S PUnit :=
  ChainComplex.mk'XIso
    (ModuleCat.of.{max v w} S P.CotangentSpace)
    (ModuleCat.of.{max v w} S (Lift P))
    (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftEquiv P).toLinearMap))
    (fun {_ _} _ => ⟨ModuleCat.of.{max v w} S PUnit, 0, CategoryTheory.Limits.zero_comp⟩)
    i

/-- Every element in a component of the naive cotangent complex in degree at
least two is zero. -/
theorem componentSuccSucc_eq_zero
    (P : Extension.{w} R S) (i : ℕ) (x : (complex P).X (i + 2)) :
    x = 0 := sorry

/-- Components of the naive cotangent complex in degrees at least two are
subsingletons. -/
theorem componentSuccSucc_subsingleton
    (P : Extension.{w} R S) (i : ℕ) :
    Subsingleton ((complex P).X (i + 2)) := sorry

section ChainMap

variable {R' : Type x} [CommRing R'] [Algebra R' S]
variable [Algebra R R'] [IsScalarTower R R' S]

/-- The degree-one and degree-zero components of the functorial naive
cotangent map form a commutative square. -/
theorem chainMapOneZeroComm
    {P : Extension.{w} R S} {Q : Extension.{w} R' S} (f : P.Hom Q) :
    ModuleCat.ofHom (liftMap f) ≫ (complex Q).d 1 0 =
      (complex P).d 1 0 ≫ ModuleCat.ofHom (CotangentSpace.map f) := sorry

/-- The zero higher component satisfies the inductive chain-map compatibility
condition for the functorial naive cotangent map. -/
theorem chainMapSuccComm
    {P : Extension.{w} R S} {Q : Extension.{w} R' S} (f : P.Hom Q) (n : ℕ)
    (p :
      Σ' (zero : (complex P).X n ⟶ (complex Q).X n)
          (one : (complex P).X (n + 1) ⟶ (complex Q).X (n + 1)),
        one ≫ (complex Q).d (n + 1) n =
          (complex P).d (n + 1) n ≫ zero) :
    (0 : (complex P).X (n + 2) ⟶ (complex Q).X (n + 2)) ≫
        (complex Q).d (n + 2) (n + 1) =
      (complex P).d (n + 2) (n + 1) ≫ p.2.1 := sorry

/-- The higher components used in the functorial naive cotangent map.  They
are canonically zero because the complex is concentrated in degrees zero and
one. -/
noncomputable def chainMapSucc
    {P : Extension.{w} R S} {Q : Extension.{w} R' S} (f : P.Hom Q) (n : ℕ)
    (p :
      Σ' (zero : (complex P).X n ⟶ (complex Q).X n)
          (one : (complex P).X (n + 1) ⟶ (complex Q).X (n + 1)),
        one ≫ (complex Q).d (n + 1) n =
          (complex P).d (n + 1) n ≫ zero) :
    Σ' two : (complex P).X (n + 2) ⟶ (complex Q).X (n + 2),
      two ≫ (complex Q).d (n + 2) (n + 1) =
        (complex P).d (n + 2) (n + 1) ≫ p.2.1 :=
  ⟨0, chainMapSuccComm f n p⟩

/-- The functorial chain map on naive cotangent complexes induced by a
morphism of algebra presentations. -/
@[stacks 07BN "functorial map of naive cotangent complexes"]
noncomputable def chainMap
    {P : Extension.{w} R S} {Q : Extension.{w} R' S} (f : P.Hom Q) :
    complex P ⟶ complex Q :=
  ChainComplex.mkHom _ _
    (ModuleCat.ofHom (CotangentSpace.map f))
    (ModuleCat.ofHom (liftMap f))
    (chainMapOneZeroComm f)
    (chainMapSucc f)

end ChainMap

/-- The naive cotangent chain map induced by the identity presentation
morphism is the identity chain map. -/
theorem chainMap_id (P : Extension.{w} R S) :
    chainMap (.id P) = 𝟙 _ := sorry

/-- Functorial naive cotangent chain maps respect composition. -/
theorem chainMap_comp
    {P Q T : Extension.{w} R S} (f : P.Hom Q) (g : Q.Hom T) :
    chainMap (g.comp f) = chainMap f ≫ chainMap g := sorry

/-- The degree-one homotopy data relating the chain maps induced by two
parallel presentation morphisms. -/
noncomputable def chainHomotopyHom
    {P Q : Extension.{w} R S} (f g : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    ((complex P).X i ⟶ (complex Q).X j) := by
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero => exact ModuleCat.ofHom (liftHomotopyMap f g)
      | succ j => exact 0
  · exact 0

/-- The difference of the functorial maps attached to two parallel
presentation morphisms is null-homotopic. -/
theorem chainMap_sub_eq_nullHomotopicMap
    {P Q : Extension.{w} R S} (f g : P.Hom Q) :
    chainMap f - chainMap g = Homotopy.nullHomotopicMap' (chainHomotopyHom f g) := sorry

/-- Any two functorial naive cotangent chain maps induced by parallel
presentation morphisms are chain-homotopic. -/
noncomputable def chainMapHomotopy
    {P Q : Extension.{w} R S} (f g : P.Hom Q) :
    Homotopy (chainMap f) (chainMap g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (chainMap_sub_eq_nullHomotopicMap f g)).trans
      (Homotopy.nullHomotopy' (chainHomotopyHom f g)))

section Generators

variable {ι ι' : Type w}

/-- The forward and backward default presentation maps are homotopy inverse on
naive cotangent complexes. -/
noncomputable def generatorsHomInvId
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators R S ι') :
    Homotopy
      (chainMap (Algebra.Generators.defaultHom P Q).toExtensionHom ≫
        chainMap (Algebra.Generators.defaultHom Q P).toExtensionHom)
      (𝟙 (complex P.toExtension)) :=
  (Homotopy.ofEq
    (chainMap_comp
      (Algebra.Generators.defaultHom P Q).toExtensionHom
      (Algebra.Generators.defaultHom Q P).toExtensionHom).symm).trans
    ((chainMapHomotopy
      ((Algebra.Generators.defaultHom Q P).toExtensionHom.comp
        (Algebra.Generators.defaultHom P Q).toExtensionHom)
      (.id P.toExtension)).trans
      (Homotopy.ofEq (chainMap_id P.toExtension)))

/-- The backward and forward default presentation maps are homotopy inverse on
naive cotangent complexes. -/
noncomputable def generatorsInvHomId
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators R S ι') :
    Homotopy
      (chainMap (Algebra.Generators.defaultHom Q P).toExtensionHom ≫
        chainMap (Algebra.Generators.defaultHom P Q).toExtensionHom)
      (𝟙 (complex Q.toExtension)) :=
  (Homotopy.ofEq
    (chainMap_comp
      (Algebra.Generators.defaultHom Q P).toExtensionHom
      (Algebra.Generators.defaultHom P Q).toExtensionHom).symm).trans
    ((chainMapHomotopy
      ((Algebra.Generators.defaultHom P Q).toExtensionHom.comp
        (Algebra.Generators.defaultHom Q P).toExtensionHom)
      (.id Q.toExtension)).trans
      (Homotopy.ofEq (chainMap_id Q.toExtension)))

/-- Naive cotangent complexes of any two presentations of the same algebra
are canonically homotopy equivalent. -/
@[stacks 07BN "presentation independence of naive cotangent complexes"]
noncomputable def generatorsHomotopyEquiv
    (P : Algebra.Generators R S ι) (Q : Algebra.Generators R S ι') :
    HomotopyEquiv (complex P.toExtension) (complex Q.toExtension) where
  hom := chainMap (Algebra.Generators.defaultHom P Q).toExtensionHom
  inv := chainMap (Algebra.Generators.defaultHom Q P).toExtensionHom
  homotopyHomInvId := generatorsHomInvId P Q
  homotopyInvHomId := generatorsInvHomId P Q

end Generators

end Algebra.Extension.NaiveCotangent
