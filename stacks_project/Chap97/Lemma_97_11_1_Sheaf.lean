/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf
public import stacks_project.Chap97.«97_11_0_1_Pair»
public import stacks_project.Chap97.«97_11_0_2_RestrictionOfScalars»

/-!
# The restriction-of-scalars fppf sheaf

The functor `Res_{Z/B}(X)` is an fppf sheaf on `Sch/S`, and morphisms of sheaves
out of an algebraic space `T` correspond to restriction-of-scalars pairs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The restriction-of-scalars functor `Res_{Z/B}(X)` is a sheaf for the fppf topology
on schemes over `S`. -/
theorem restrictionOfScalars_isSheaf {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (restrictionOfScalars f g) :=
  sorry

/-- The restriction-of-scalars sheaf `Res_{Z/B}(X)` on `(Sch/S)_fppf`. -/
def restrictionOfScalarsSheaf {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨restrictionOfScalars f g, restrictionOfScalars_isSheaf f g⟩

/-- The underlying presheaf of `restrictionOfScalarsSheaf` is `restrictionOfScalars`. -/
theorem restrictionOfScalarsSheaf_obj {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) :
    (restrictionOfScalarsSheaf f g).obj = restrictionOfScalars f g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- The structure morphism `Res_{Z/B}(X) ⟶ B` of fppf sheaves. -/
def toUliftSheaf {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B) :
    restrictionOfScalarsSheaf f g ⟶ uliftSheaf B :=
  Sheaf.homEquiv.symm (toFunctorOfPoints f g)

/-- The underlying presheaf morphism of `toUliftSheaf` is `toFunctorOfPoints`. -/
theorem toUliftSheaf_hom {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) :
    (toUliftSheaf f g).hom = toFunctorOfPoints f g :=
  sorry

/-- The fibre product projections of `fiber g a` form a commutative square over `B`. -/
theorem fiber_condition {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) :
    fiberFst g a ≫ a = fiberSnd g a ≫ g :=
  sorry

/-- The comparison `T ×_{a,B} Z ⟶ pullback a g` from the scheme-level fibre product
to the categorical fibre product of algebraic spaces. -/
def fiberToPullback {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) :
    fiber g a ⟶ pullback a g :=
  pullback.lift (fiberFst g a) (fiberSnd g a) (fiber_condition g a)

/-- The categorical fibre product projections of `pullback a g` form a commutative
square over `B`. -/
theorem pullback_condition {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) :
    pullback.fst a g ≫ a = pullback.snd a g ≫ g :=
  sorry

/-- The comparison `pullback a g ⟶ T ×_{a,B} Z` from the categorical fibre product
to the scheme-level fibre product. -/
def pullbackToFiber {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) :
    pullback a g ⟶ fiber g a :=
  pullbackLift a g (pullback.fst a g) (pullback.snd a g) (pullback_condition g a)

/-- The canonical isomorphism between the scheme-level fibre product `fiber g a`
and the categorical fibre product `pullback a g`. -/
def fiberIsoPullback {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) :
    fiber g a ≅ pullback a g where
  hom := fiberToPullback g a
  inv := pullbackToFiber g a
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction-of-scalars pairs over a scheme `T`, as an algebraic space, correspond to
the scheme-level pairs used as values of `restrictionOfScalars`. -/
def pairOverEquiv {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
    (T : Over S) :
    RestrictScalars.Pair f g (ofOver T) ≃ Pair f g T where
  toFun p :=
    { base := p.a
      lift := (fiberIsoPullback g p.a).hom ≫ p.b
      overZ := sorry }
  invFun p :=
    { a := p.base
      b := (fiberIsoPullback g p.base).inv ≫ p.lift
      overZ := sorry }
  left_inv := sorry
  right_inv := sorry

/-- The base morphism of `pairOverEquiv` is the algebraic-space morphism `a`. -/
theorem pairOverEquiv_base {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) {T : Over S} (p : RestrictScalars.Pair f g (ofOver T)) :
    (pairOverEquiv f g T p).base = p.a :=
  sorry

/-- The lift of `pairOverEquiv` is the composite of `fiberIsoPullback.hom` with `b`. -/
theorem pairOverEquiv_lift {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) {T : Over S} (p : RestrictScalars.Pair f g (ofOver T)) :
    (pairOverEquiv f g T p).lift = (fiberIsoPullback g p.a).hom ≫ p.b :=
  sorry

/-- The presheaf morphism associated to a restriction-of-scalars pair over an algebraic
space, sending a scheme-valued point of `T` to the restricted pair. -/
def ofPair_hom {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (p : RestrictScalars.Pair f g T) :
    (uliftSheaf T).obj ⟶ (restrictionOfScalarsSheaf f g).obj where
  app U := TypeCat.ofHom fun x ↦
    pairOverEquiv f g U.unop
      (RestrictScalars.Pair.map p (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T))
  naturality := sorry

/-- The sheaf morphism `T ⟶ Res_{Z/B}(X)` associated to a pair `(a, b)` over `T`. -/
def ofPair {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (p : RestrictScalars.Pair f g T) :
    uliftSheaf T ⟶ restrictionOfScalarsSheaf f g :=
  Sheaf.homEquiv.symm (ofPair_hom p)

/-- Components of `ofPair` restrict the algebraic-space pair along the underlying
`T`-point. -/
theorem ofPair_hom_app {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (p : RestrictScalars.Pair f g T) (U : (Over S)ᵒᵖ)
    (x : ULift.{u + 1} (T.functorOfPoints.obj U)) :
    (ofPair p).hom.app U x =
      pairOverEquiv f g U.unop
        (RestrictScalars.Pair.map p (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T)) :=
  sorry

/-- The morphism `a : T ⟶ B` recovered from a sheaf map `T ⟶ Res_{Z/B}(X)` by the
structure morphism `Res ⟶ B` and full faithfulness of universe lifting. -/
def toPair_a {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) : T ⟶ B :=
  (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight (Over S)ᵒᵖ).preimage
    (v ≫ toUliftSheaf f g).hom

/-- The restriction-of-scalars pair over a scheme obtained by evaluating a sheaf map
on a `T`-point. -/
def toPairEval {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) {U : (Over S)ᵒᵖ}
    (t : T.functorOfPoints.obj U) : Pair f g U.unop :=
  (v.hom.app U) (ULift.up t)

/-- The `T`-point of a `U`-point of `T ×_{a,B} Z`. -/
def toPairFst {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    T.functorOfPoints.obj U :=
  (pullback.fst (toPair_a v) g).app U x

/-- The `Z`-point of a `U`-point of `T ×_{a,B} Z`. -/
def toPairSnd {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    Z.functorOfPoints.obj U :=
  (pullback.snd (toPair_a v) g).app U x

/-- The canonical section of `U ×_{a_U,B} Z` over a `U`-point of `T ×_{a,B} Z` lies
over `B`. -/
theorem toPairSection_overB {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    𝟙 (ofOver U.unop) ≫ (toPairEval v (toPairFst v x)).base =
      (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z) ≫ g :=
  sorry

/-- The canonical section `U ⟶ U ×_{a_U,B} Z` of a `U`-point of `T ×_{a,B} Z`. -/
def toPairSection {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    ofOver U.unop ⟶ fiber g (toPairEval v (toPairFst v x)).base :=
  pullbackLift (toPairEval v (toPairFst v x)).base g (𝟙 _)
    (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z)
    (toPairSection_overB v x)

/-- The morphism `T ×_{a,B} Z ⟶ X` recovered from a sheaf map `T ⟶ Res_{Z/B}(X)`. -/
def toPair_b {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) :
    pullback (toPair_a v) g ⟶ X where
  app U := TypeCat.ofHom fun x ↦
    yonedaEquiv (toPairSection v x ≫ (toPairEval v (toPairFst v x)).lift)
  naturality := sorry

/-- The restriction-of-scalars pair over `T` associated to a sheaf morphism
`T ⟶ Res_{Z/B}(X)`. -/
def toPair {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) :
    RestrictScalars.Pair f g T where
  a := toPair_a v
  b := toPair_b v
  overZ := sorry

/-- Sheaf morphisms `T ⟶ Res_{Z/B}(X)` correspond to restriction-of-scalars pairs
over the algebraic space `T`. -/
def homEquiv {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B) :
    (uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) ≃ RestrictScalars.Pair f g T where
  toFun := toPair
  invFun := ofPair
  left_inv := sorry
  right_inv := sorry

/-- `homEquiv` sends a sheaf morphism to the associated pair. -/
theorem homEquiv_apply {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (v : uliftSheaf T ⟶ restrictionOfScalarsSheaf f g) :
    homEquiv f g v = toPair v :=
  sorry

/-- The inverse of `homEquiv` sends a pair to the associated sheaf morphism. -/
theorem homEquiv_symm_apply {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (p : RestrictScalars.Pair f g T) :
    (homEquiv f g).symm p = ofPair p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
