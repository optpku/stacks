module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Reindex
public import Mathlib.Algebra.DirectSum.Ring

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology

variable {S X : Scheme.{u}} (delta : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction delta] [LocallyOfFiniteType p]

/-- The structure morphism of `Over.mk p` inherits local finite type from `p`. -/
instance instLocallyOfFiniteTypeOverMk : LocallyOfFiniteType (Over.mk p).hom := inferInstance

/-- The degree-`n` group `Aⁿ(X ⟶ X)` of concrete bivariant classes on the identity of
`Over.mk p`. -/
abbrev degree (n : ℤ) : Type (u + 1) :=
  BivariantClass delta (𝟙 (Over.mk p)) n

/-- The degree-`n` piece is the concrete bivariant-class carrier of the identity of
`Over.mk p`. -/
theorem degree_def (n : ℤ) :
    degree delta p n =
      BivariantClass delta (𝟙 (Over.mk p)) n := sorry

/-- The pointwise-zero cap family on the identity of `Over.mk p`. -/
def zeroCap (n : ℤ) : BivariantClass.CapFamily delta (𝟙 (Over.mk p)) n :=
  fun {_ _} _ _ _ _ _ _ _ _ ↦ 0

/-- Evaluation of the zero cap family is the zero additive map. -/
theorem zeroCap_apply (n : ℤ) {X' Y' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    zeroCap delta p n i f' g square k = 0 := sorry

/-- The zero cap family satisfies proper-pushforward compatibility. -/
theorem zeroMapProper (n : ℤ) :
    BivariantClass.CompatibleWithProperPushforward delta (zeroCap delta p n) := sorry

/-- The zero cap family satisfies flat-pullback compatibility. -/
theorem zeroPullbackFlat (n : ℤ) :
    BivariantClass.CompatibleWithFlatPullback delta (zeroCap delta p n) := sorry

/-- The zero cap family satisfies effective-Cartier Gysin compatibility. -/
theorem zeroGysinCartier (n : ℤ) :
    BivariantClass.CompatibleWithCartierGysin delta
      (zeroCap delta p n) := sorry

/-- The zero bivariant class, with pointwise zero cap action. -/
def zeroClass (n : ℤ) : degree delta p n where
  cap := zeroCap delta p n
  map_proper := zeroMapProper delta p n
  pullback_flat := zeroPullbackFlat delta p n
  gysin_cartier := zeroGysinCartier delta p n

/-- The zero class acts by the zero additive map. -/
theorem zeroClass_apply (n : ℤ) {X' Y' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (zeroClass delta p n).cap i f' g square k = 0 := sorry

/-- Pointwise addition of two cap families on the identity of `Over.mk p`. -/
def addCap {n : ℤ} (a b : degree delta p n) :
    BivariantClass.CapFamily delta (𝟙 (Over.mk p)) n :=
  fun {_ _} _ _ i f' g _ square k ↦
    a.cap i f' g square k + b.cap i f' g square k

/-- Evaluation of pointwise cap-family addition is addition of the evaluated maps. -/
theorem addCap_apply {n : ℤ} (a b : degree delta p n)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    addCap delta p a b i f' g square k =
      a.cap i f' g square k + b.cap i f' g square k := sorry

/-- The sum of two cap families satisfies proper-pushforward compatibility. -/
theorem addMapProper {n : ℤ} (a b : degree delta p n) :
    BivariantClass.CompatibleWithProperPushforward delta
      (addCap delta p a b) := sorry

/-- The sum of two cap families satisfies flat-pullback compatibility. -/
theorem addPullbackFlat {n : ℤ} (a b : degree delta p n) :
    BivariantClass.CompatibleWithFlatPullback delta
      (addCap delta p a b) := sorry

/-- The sum of two cap families satisfies effective-Cartier Gysin compatibility. -/
theorem addGysinCartier {n : ℤ} (a b : degree delta p n) :
    BivariantClass.CompatibleWithCartierGysin delta
      (addCap delta p a b) := sorry

/-- Addition of bivariant classes, defined pointwise on cap actions. -/
def addClass {n : ℤ} (a b : degree delta p n) :
    degree delta p n where
  cap := addCap delta p a b
  map_proper := addMapProper delta p a b
  pullback_flat := addPullbackFlat delta p a b
  gysin_cartier := addGysinCartier delta p a b

/-- The sum class acts by the pointwise sum of the two cap maps. -/
theorem addClass_apply {n : ℤ} (a b : degree delta p n) {X' Y' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (addClass delta p a b).cap i f' g square k =
      a.cap i f' g square k + b.cap i f' g square k := sorry

/-- Pointwise negation of a cap family on the identity of `Over.mk p`. -/
def negCap {n : ℤ} (a : degree delta p n) :
    BivariantClass.CapFamily delta (𝟙 (Over.mk p)) n :=
  fun {_ _} _ _ i f' g _ square k ↦ -a.cap i f' g square k

/-- Evaluation of pointwise cap-family negation is negation of the evaluated map. -/
theorem negCap_apply {n : ℤ} (a : degree delta p n)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    negCap delta p a i f' g square k = -a.cap i f' g square k := sorry

/-- The negative of a cap family satisfies proper-pushforward compatibility. -/
theorem negMapProper {n : ℤ} (a : degree delta p n) :
    BivariantClass.CompatibleWithProperPushforward delta
      (negCap delta p a) := sorry

/-- The negative of a cap family satisfies flat-pullback compatibility. -/
theorem negPullbackFlat {n : ℤ} (a : degree delta p n) :
    BivariantClass.CompatibleWithFlatPullback delta
      (negCap delta p a) := sorry

/-- The negative of a cap family satisfies effective-Cartier Gysin compatibility. -/
theorem negGysinCartier {n : ℤ} (a : degree delta p n) :
    BivariantClass.CompatibleWithCartierGysin delta
      (negCap delta p a) := sorry

/-- Negation of a bivariant class, defined pointwise on cap actions. -/
def negClass {n : ℤ} (a : degree delta p n) :
    degree delta p n where
  cap := negCap delta p a
  map_proper := negMapProper delta p a
  pullback_flat := negPullbackFlat delta p a
  gysin_cartier := negGysinCartier delta p a

/-- The negative class acts by the pointwise negative cap map. -/
theorem negClass_apply {n : ℤ} (a : degree delta p n) {X' Y' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (negClass delta p a).cap i f' g square k = -a.cap i f' g square k := sorry

/-- Repeated addition of a concrete bivariant class. -/
def nsmulClass {n : ℤ} (a : degree delta p n) : ℕ → degree delta p n
  | 0 => zeroClass delta p n
  | m + 1 => addClass delta p (nsmulClass a m) a

/-- Repeated addition starts with the pointwise-zero class. -/
theorem nsmulClass_zero {n : ℤ} (a : degree delta p n) :
    nsmulClass delta p a 0 = zeroClass delta p n := sorry

/-- Repeated addition at a successor adds one further copy. -/
theorem nsmulClass_succ {n : ℤ} (a : degree delta p n) (m : ℕ) :
    nsmulClass delta p a (m + 1) = addClass delta p (nsmulClass delta p a m) a := sorry

/-- Signed repeated addition of a concrete bivariant class. -/
def zsmulClass {n : ℤ} (a : degree delta p n) : ℤ → degree delta p n
  | .ofNat m => nsmulClass delta p a m
  | .negSucc m => negClass delta p (nsmulClass delta p a (m + 1))

/-- Signed repeated addition agrees with natural repeated addition on nonnegative integers. -/
theorem zsmulClass_ofNat {n : ℤ} (a : degree delta p n) (m : ℕ) :
    zsmulClass delta p a m = nsmulClass delta p a m := sorry

/-- Zero is a left identity for pointwise addition of bivariant classes. -/
theorem zero_add_degree {n : ℤ} (a : degree delta p n) :
    addClass delta p (zeroClass delta p n) a = a := sorry

/-- Zero is a right identity for pointwise addition of bivariant classes. -/
theorem add_zero_degree {n : ℤ} (a : degree delta p n) :
    addClass delta p a (zeroClass delta p n) = a := sorry

/-- Pointwise addition of bivariant classes is associative. -/
theorem add_assoc_degree {n : ℤ} (a b c : degree delta p n) :
    addClass delta p (addClass delta p a b) c =
      addClass delta p a (addClass delta p b c) := sorry

/-- Pointwise addition of bivariant classes is commutative. -/
theorem add_comm_degree {n : ℤ} (a b : degree delta p n) :
    addClass delta p a b = addClass delta p b a := sorry

/-- Pointwise negation is a left additive inverse. -/
theorem neg_add_cancel_degree {n : ℤ} (a : degree delta p n) :
    addClass delta p (negClass delta p a) a = zeroClass delta p n := sorry

/-- Subtraction is pointwise addition of the negative class. -/
theorem sub_eq_add_neg_degree {n : ℤ} (a b : degree delta p n) :
    addClass delta p a (negClass delta p b) =
      addClass delta p a (negClass delta p b) := sorry

/-- Natural scalar multiplication by zero gives the zero bivariant class. -/
theorem nsmul_zero_degree {n : ℤ} (a : degree delta p n) :
    nsmulClass delta p a 0 = zeroClass delta p n := sorry

/-- Natural scalar multiplication at a successor adds one further copy. -/
theorem nsmul_succ_degree {n : ℤ} (m : ℕ) (a : degree delta p n) :
    nsmulClass delta p a (m + 1) =
      addClass delta p (nsmulClass delta p a m) a := sorry

/-- Integer scalar multiplication by zero gives the zero bivariant class. -/
theorem zsmul_zero_degree {n : ℤ} (a : degree delta p n) :
    zsmulClass delta p a 0 = zeroClass delta p n := sorry

/-- Integer scalar multiplication at a positive successor adds one further copy. -/
theorem zsmul_succ_degree {n : ℤ} (m : ℕ) (a : degree delta p n) :
    zsmulClass delta p a (.ofNat (m + 1)) =
      addClass delta p (zsmulClass delta p a (.ofNat m)) a := sorry

/-- Integer scalar multiplication at a negative successor is the corresponding negative. -/
theorem zsmul_neg_degree {n : ℤ} (m : ℕ) (a : degree delta p n) :
    zsmulClass delta p a (.negSucc m) =
      negClass delta p (zsmulClass delta p a (.ofNat (m + 1))) := sorry

/-- Every concrete bivariant degree is an additive commutative group under pointwise
operations. -/
instance instAddCommGroupDegree (n : ℤ) : AddCommGroup (degree delta p n) where
  zero := zeroClass delta p n
  add := addClass delta p
  neg := negClass delta p
  sub := fun a b ↦ addClass delta p a (negClass delta p b)
  zero_add := zero_add_degree delta p
  add_zero := add_zero_degree delta p
  add_assoc := add_assoc_degree delta p
  add_comm := add_comm_degree delta p
  neg_add_cancel := neg_add_cancel_degree delta p
  nsmul := fun m a ↦ nsmulClass delta p a m
  nsmul_zero := nsmul_zero_degree delta p
  nsmul_succ := nsmul_succ_degree delta p
  zsmul := fun m a ↦ zsmulClass delta p a m
  zsmul_zero' := zsmul_zero_degree delta p
  zsmul_succ' := zsmul_succ_degree delta p
  zsmul_neg' := zsmul_neg_degree delta p
  sub_eq_add_neg := sub_eq_add_neg_degree delta p

/-- The degree calculation for composing classes of degrees `i` and `j`. -/
theorem compositionDegree (k i j : ℤ) :
    (k - j) - i = k - (i + j) := sorry

/-- The cap family obtained by composing two identity-morphism bivariant classes. -/
def mulCap {i j : ℤ} (a : degree delta p i)
    (b : degree delta p j) :
    BivariantClass.CapFamily delta (𝟙 (Over.mk p)) (i + j) :=
  fun {_ Y'} _ _ l f' g _ square k ↦
    (RelativeChow.castDegree delta (X := _) (compositionDegree k i j)).comp
      ((a.cap l f' g square (k - j)).comp
        (b.cap g (𝟙 Y') g IsPullback.of_id_snd k))

/-- Composed cap families satisfy proper-pushforward compatibility. -/
theorem mulMapProper {i j : ℤ} (a : degree delta p i)
    (b : degree delta p j) :
    BivariantClass.CompatibleWithProperPushforward delta
      (mulCap delta p a b) := sorry

/-- Composed cap families satisfy flat-pullback compatibility. -/
theorem mulPullbackFlat {i j : ℤ} (a : degree delta p i)
    (b : degree delta p j) :
    BivariantClass.CompatibleWithFlatPullback delta
      (mulCap delta p a b) := sorry

/-- Composed cap families satisfy effective-Cartier Gysin compatibility. -/
theorem mulGysinCartier {i j : ℤ} (a : degree delta p i)
    (b : degree delta p j) :
    BivariantClass.CompatibleWithCartierGysin delta
      (mulCap delta p a b) := sorry

/-- Homogeneous multiplication is composition of concrete bivariant classes. -/
def mul {i j : ℤ} (a : degree delta p i)
    (b : degree delta p j) : degree delta p (i + j) where
  cap := mulCap delta p a b
  map_proper := mulMapProper delta p a b
  pullback_flat := mulPullbackFlat delta p a b
  gysin_cartier := mulGysinCartier delta p a b

/-- Homogeneous multiplication is computed pointwise by composition of cap operations. -/
theorem mul_cap {i j : ℤ} (a : degree delta p i) (b : degree delta p j)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (l : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback l.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (mul delta p a b).cap l f' g square k = mulCap delta p a b l f' g square k := sorry

/-- The inverse underlying map of an isomorphism in `Over S` defines a morphism in the
opposite direction. -/
theorem inverseOver_fac {X' Y' : Over S} (f' : X' ⟶ Y') [IsIso f'.left] :
    inv f'.left ≫ X'.hom = Y'.hom := sorry

/-- The inverse over-morphism determined by an isomorphism on underlying schemes. -/
def inverseOver {X' Y' : Over S} (f' : X' ⟶ Y') [IsIso f'.left] : Y' ⟶ X' :=
  Over.homMk (inv f'.left) (inverseOver_fac f')

/-- The underlying map of `inverseOver f'` is the inverse of the underlying map of `f'`. -/
theorem inverseOver_left {X' Y' : Over S} (f' : X' ⟶ Y') [IsIso f'.left] :
    (inverseOver f').left = inv f'.left := sorry

/-- The underlying map of `inverseOver f'` is an isomorphism. -/
instance inverseOverLeftIsIso {X' Y' : Over S} (f' : X' ⟶ Y') [IsIso f'.left] :
    IsIso (inverseOver f').left := sorry

/-- An identity pullback square induces the cap family of the degree-zero identity class. -/
def identityCap : BivariantClass.CapFamily delta (𝟙 (Over.mk p)) 0 :=
  fun {X' Y'} _ _ _ f' _ _ square k ↦
    -- The displayed pullback of `𝟙 (Over.mk p)` proves this particular top map is an isomorphism.
    -- Local instance justification (proof-local temporary data): this `square` alone supplies `IsIso f'.left`.
    letI : IsIso f'.left := square.isIso_snd_of_isIso
    -- An inverse isomorphism of schemes is proper, as required by proper pushforward on Chow groups.
    -- Local instance justification (proof-local temporary data): this inverse of `f'` is used only in this cap value.
    letI : IsProper (inverseOver f').left := MorphismProperty.of_isIso @IsProper _
    RelativeChow.castDegree delta (X := X') (Int.sub_zero k).symm |>.comp
      (ChowGroup.map delta Y' X' (inverseOver f') k)

/-- The identity cap family satisfies proper-pushforward compatibility. -/
theorem identityMapProper :
    BivariantClass.CompatibleWithProperPushforward delta (identityCap delta p) := sorry

/-- The identity cap family satisfies flat-pullback compatibility. -/
theorem identityPullbackFlat :
    BivariantClass.CompatibleWithFlatPullback delta (identityCap delta p) := sorry

/-- The identity cap family satisfies effective-Cartier Gysin compatibility. -/
theorem identityGysinCartier :
    BivariantClass.CompatibleWithCartierGysin delta
      (identityCap delta p) := sorry

/-- The degree-zero identity bivariant class. -/
def one : degree delta p 0 where
  cap := identityCap delta p
  map_proper := identityMapProper delta p
  pullback_flat := identityPullbackFlat delta p
  gysin_cartier := identityGysinCartier delta p

/-- The degree-zero identity class acts by the canonical identity cap map. -/
theorem one_cap {X' Y' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (one delta p).cap i f' g square k = identityCap delta p i f' g square k := sorry

/-- Homogeneous multiplication by zero on the right vanishes. -/
theorem mul_zero {i j : ℤ} (a : degree delta p i) :
    mul delta p a (0 : degree delta p j) = 0 := sorry

/-- Homogeneous multiplication by zero on the left vanishes. -/
theorem zero_mul {i j : ℤ} (b : degree delta p j) :
    mul delta p (0 : degree delta p i) b = 0 := sorry

/-- Homogeneous multiplication distributes over addition in the right variable. -/
theorem mul_add {i j : ℤ} (a : degree delta p i)
    (b c : degree delta p j) :
    mul delta p a (b + c) =
      mul delta p a b + mul delta p a c := sorry

/-- Homogeneous multiplication distributes over addition in the left variable. -/
theorem add_mul {i j : ℤ} (a b : degree delta p i)
    (c : degree delta p j) :
    mul delta p (a + b) c =
      mul delta p a c + mul delta p b c := sorry

/-- Bivariant composition supplies the additive graded multiplication data. -/
instance instGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (degree delta p) where
  mul := fun a b ↦ mul delta p a b
  mul_zero := mul_zero delta p
  zero_mul := zero_mul delta p
  mul_add := mul_add delta p
  add_mul := add_mul delta p

/-- The identity bivariant class supplies the graded unit data. -/
instance instGOne : GradedMonoid.GOne (degree delta p) where
  one := one delta p

/-- The identity bivariant class is a left identity for homogeneous composition. -/
theorem one_mul (a : GradedMonoid (degree delta p)) :
    (1 : GradedMonoid (degree delta p)) * a = a := sorry

/-- The identity bivariant class is a right identity for homogeneous composition. -/
theorem mul_one (a : GradedMonoid (degree delta p)) :
    a * (1 : GradedMonoid (degree delta p)) = a := sorry

/-- Homogeneous bivariant composition is associative. -/
theorem mul_assoc (a b c : GradedMonoid (degree delta p)) :
    a * b * c = a * (b * c) := sorry

/-- Identity-morphism bivariant classes form a graded monoid under composition. -/
instance instGMonoid : GradedMonoid.GMonoid (degree delta p) where
  one_mul := one_mul delta p
  mul_one := mul_one delta p
  mul_assoc := mul_assoc delta p

/-- The natural-number cast in degree zero. -/
def natCast (n : ℕ) : degree delta p 0 := n • one delta p

/-- The degree-zero natural-number cast sends zero to zero. -/
theorem natCast_zero : natCast delta p 0 = 0 := sorry

/-- The degree-zero natural-number cast respects successors. -/
theorem natCast_succ (n : ℕ) :
    natCast delta p (n + 1) =
      natCast delta p n + one delta p := sorry

/-- Identity-morphism bivariant classes form a graded semiring. -/
instance instGSemiring : DirectSum.GSemiring (degree delta p) where
  natCast := natCast delta p
  natCast_zero := natCast_zero delta p
  natCast_succ := natCast_succ delta p

/-- The integer cast in degree zero. -/
def intCast (z : ℤ) : degree delta p 0 := z • one delta p

/-- The degree-zero integer cast extends the natural-number cast. -/
theorem intCast_ofNat (n : ℕ) :
    intCast delta p n = natCast delta p n := sorry

/-- The degree-zero integer cast has the canonical negative-successor value. -/
theorem intCast_negSucc (n : ℕ) :
    intCast delta p (Int.negSucc n) =
      -natCast delta p (n + 1) := sorry

/-- Identity-morphism bivariant classes form a graded ring, without a commutativity claim. -/
instance instGRing : DirectSum.GRing (degree delta p) where
  intCast := intCast delta p
  intCast_ofNat := intCast_ofNat delta p
  intCast_negSucc_ofNat := intCast_negSucc delta p

/-- The Chow cohomology ring `A⁎(X)` as the external direct sum of its concrete bivariant
degrees. -/
abbrev ring : Type (u + 1) := ⨁ n : ℤ, degree delta p n

/-- Chow cohomology is the external direct sum of the identity bivariant-class groups. -/
theorem ring_def :
    ring delta p = (⨁ n : ℤ, degree delta p n) := sorry

/-- Products of homogeneous inclusions are induced by bivariant composition. -/
theorem of_mul_of {i j : ℤ} (a : degree delta p i)
    (b : degree delta p j) :
    DirectSum.of (degree delta p) i a *
        DirectSum.of (degree delta p) j b =
      DirectSum.of (degree delta p) (i + j)
        (mul delta p a b) := sorry

end AlgebraicGeometry.ChowCohomology
