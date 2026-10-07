module

public import stacks_project.Chap108.Lemma_108_5_10_Tensor
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import ReasLib.RingTheory.Polynomial.Numerical
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»

/-!
# Hilbert-polynomial loci of the Grothendieck Quot functor

The open-and-closed locus `Quot^P_{F/X/B}` is the subfunctor of Chap99 `quot` on
classes whose representatives have Hilbert polynomial `P` with respect to a
fixed invertible module `L`. Tensoring with `L` shifts this polynomial by
`P'(t) = P(t + 1)`. Euler characteristics are the Chap72 formula, isolated
through the Chap99-available `schemeEtaleRingedHom` comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalCategory.InvertiblePower
open CategoryTheory.MorphismProperty


universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and
-- `Modules.higherDirectImage` pin the Abelian-induced `Preadditive` /
-- `HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Direct image from the étale module site of a representable algebraic space to
the Zariski module site of its underlying scheme. -/
def ofOverToScheme (U : Over S) :
    (ofOver U).Modules ⥤ U.left.Modules :=
  (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
    (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ⋙
      opensToSchemeModules U.left

/-- `ofOverToScheme U` is the composite of the two ringed-site module pushforwards
with the open-to-scheme comparison. -/
theorem ofOverToScheme_eq (U : Over S) :
    ofOverToScheme U =
      (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
        (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ⋙
          opensToSchemeModules U.left :=
  sorry

/-- The numerical polynomial `P'(t) = P(t + 1)` obtained by shifting the argument
of `P` by one. -/
def shiftPolynomial (P : ℤ → ℤ) : ℤ → ℤ :=
  fun t ↦ P (t + 1)

/-- `shiftPolynomial P` evaluates by incrementing the argument of `P`. -/
theorem shiftPolynomial_apply (P : ℤ → ℤ) (t : ℤ) :
    shiftPolynomial P t = P (t + 1) :=
  sorry

/-- Shifting the argument of a numerical polynomial yields a numerical
polynomial. -/
theorem isNumericalPolynomial_shiftPolynomial {P : ℤ → ℤ}
    (hP : IsNumericalPolynomial P) :
    IsNumericalPolynomial (shiftPolynomial P) :=
  sorry

/-- Euler characteristic of a coherent module on an algebraic space over a field,
as the graded Euler characteristic of its cohomology over that field. Properness
of `π` is not assumed: the source Hilbert polynomial uses proper support of the
quotient rather than properness of the ambient fibre. -/
def residueFibreEulerChar {k : Type u} [Field k] {Y : AlgebraicSpace S}
    (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    [Abelian Y.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions Y.Modules]
    (G : Y.Modules) [G.IsCoherent] : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ)
    (fun i : ℕ ↦
      (@moduleSpecΓFunctor (CommRingCat.of k)).obj
        ((ofOverToScheme (Over.mk σ)).obj (Modules.higherDirectImage π G i)))

/-- `residueFibreEulerChar` is the graded Euler characteristic of cohomology
modules over the residue field. -/
theorem residueFibreEulerChar_eq {k : Type u} [Field k] {Y : AlgebraicSpace S}
    (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    [Abelian Y.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions Y.Modules]
    (G : Y.Modules) [G.IsCoherent] :
    residueFibreEulerChar σ π G =
      GradedObject.eulerChar (ComplexShape.up ℕ)
        (fun i : ℕ ↦
          (@moduleSpecΓFunctor (CommRingCat.of k)).obj
            ((ofOverToScheme (Over.mk σ)).obj (Modules.higherDirectImage π G i))) :=
  sorry

/-- If `G` is supported on a closed subspace `W` whose structure morphism is proper
over `Spec(K)`, then `residueFibreEulerChar` of `G` agrees with the Euler
characteristic of the restriction of `G` to `W`. -/
theorem residueFibreEulerChar_eq_closedSubspace
    {k : Type u} [Field k] {Y : AlgebraicSpace S}
    (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    [Abelian Y.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions Y.Modules]
    (G : Y.Modules) [G.IsCoherent] (W : ClosedSubspace Y)
    [AlgebraicGeometry.AlgebraicSpace.Proper (W.ι ≫ π)]
    [Abelian W.X.Modules] [HasInjectiveResolutions W.X.Modules]
    [hG : ((Modules.pullback W.ι).obj G).IsCoherent]
    (hsupp : Modules.moduleSupport G ⊆ W.pointsSet) :
    residueFibreEulerChar σ π G =
      residueFibreEulerChar σ (W.ι ≫ π) ((Modules.pullback W.ι).obj G) :=
  sorry

/-- The `n`th tensor twist of the quotient module of a Quot-point by `L_T`. -/
def QuotPoint.twist {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ) : (fiber f σ).Modules :=
  eval (fiberF f L σ) Q.point.module n

/-- `QuotPoint.twist Q L n` is `InvertiblePower.eval L_T Q n`. -/
theorem QuotPoint.twist_eq {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ) :
    Q.twist L n = eval (fiberF f L σ) Q.point.module n :=
  sorry

/-- The residue-field fibre of a twist: pull `Q ⊗ L_T^{⊗ n}` back to
`X_T ×_T Spec(K)` along a field-valued point of the test scheme. -/
def QuotPoint.twistFiber {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) :
    (Limits.pullback (Limits.pullback.snd f σ.hom) t.hom).Modules :=
  (Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f σ.hom) t.hom)).obj
    (Q.twist L n)

/-- `twistFiber` is module pullback of the twist along the projection to `X_T`. -/
theorem QuotPoint.twistFiber_eq {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) :
    Q.twistFiber L n t =
      (Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f σ.hom) t.hom)).obj
        (Q.twist L n) :=
  sorry

/-- Residue-field fibres of algebraic spaces have abelian module categories. -/
instance instAbelian_fieldValuedPullback {T Y : AlgebraicSpace S} (g : Y ⟶ T)
    (t : FieldValuedPoint T) :
    Abelian (Limits.pullback g t.hom).Modules :=
  sorry

/-- The étale module category of `Spec(K)` over `S` is abelian. -/
instance instAbelian_ofOver_specField {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) :
    Abelian (ofOver (Over.mk σ)).Modules :=
  sorry

/-- Residue-field fibres of algebraic spaces have injective resolutions of
modules. -/
instance instHasInjectiveResolutions_fieldValuedPullback {T Y : AlgebraicSpace S}
    (g : Y ⟶ T) (t : FieldValuedPoint T) :
    HasInjectiveResolutions (Limits.pullback g t.hom).Modules :=
  sorry

/-- Twisted residue-field fibres of Quot-points are coherent. -/
instance instIsCoherent_twistFiber {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) :
    (Q.twistFiber L n t).IsCoherent :=
  sorry

/-- Euler characteristic `χ(X_t, Q_t ⊗ L_t^{⊗ n})` of a twisted Quot-point fibre. -/
def QuotPoint.twistEulerChar {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) : ℤ :=
  residueFibreEulerChar t.structureHom
    (Limits.pullback.snd (Limits.pullback.snd f σ.hom) t.hom)
    (Q.twistFiber L n t)

/-- `twistEulerChar` is `residueFibreEulerChar` of the twisted residue-field
fibre. -/
theorem QuotPoint.twistEulerChar_eq {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (n : ℤ)
    (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)) :
    Q.twistEulerChar L n t =
      residueFibreEulerChar t.structureHom
        (Limits.pullback.snd (Limits.pullback.snd f σ.hom) t.hom)
        (Q.twistFiber L n t) :=
  sorry

/-- A Quot-point has Hilbert polynomial `P` with respect to `L` when for every
integer `n` and every field-valued point `t` of the test scheme,
`χ(X_t, Q_t ⊗ L_t^{⊗ n}) = P n`. -/
def QuotPoint.HasHilbertPolynomial {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) : Prop :=
  ∀ (n : ℤ) (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)),
    Q.twistEulerChar L n t = P n

/-- The Hilbert polynomial condition is the fibrewise identity
`χ(X_t, Q_t ⊗ L_t^{⊗ n}) = P n`. -/
theorem QuotPoint.hasHilbertPolynomial_iff {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :
    Q.HasHilbertPolynomial L P ↔
      ∀ (n : ℤ) (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)),
        Q.twistEulerChar L n t = P n :=
  sorry

/-- A Quot-point has Hilbert polynomial `P` with respect to `L` if and only if the
tensored Quot-point has Hilbert polynomial `shiftPolynomial P` with respect to
the same `L`. -/
theorem tensor_hasHilbertPolynomial {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :
    Q.HasHilbertPolynomial L P ↔
      (Q.tensor L).HasHilbertPolynomial L (shiftPolynomial P) :=
  sorry

/-- The Hilbert-polynomial locus `Quot^P_{F/X/B}` inside `Quot_{F/X/B}`, as the
subfunctor of kernel-identified classes admitting a representative with Hilbert
polynomial `P` with respect to `L`. -/
def quotHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    Subfunctor (quot f F) where
  obj σ :=
    setOf fun q ↦
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasHilbertPolynomial L P
  map := sorry

/-- A class lies in `quotHilbert` if and only if some representing Quot-point has
Hilbert polynomial `P` with respect to `L`. -/
theorem mem_quotHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ)
    {σ : (SchemesOver B)ᵒᵖ} (q : (quot f F).obj σ) :
    q ∈ (quotHilbert f F L P).obj σ ↔
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasHilbertPolynomial L P :=
  sorry

/-- The inclusion of the Hilbert locus into the ambient Quot functor. -/
def quotHilbertι (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    (quotHilbert f F L P).toFunctor ⟶ quot f F :=
  (quotHilbert f F L P).ι

/-- `quotHilbertι` is the subfunctor inclusion of `quotHilbert`. -/
theorem quotHilbertι_eq (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    quotHilbertι f F L P = (quotHilbert f F L P).ι :=
  sorry

/-- Scheme-level open immersions, as a morphism property on schemes over `B`. -/
def openImmersionSchemesOver : MorphismProperty (SchemesOver B) :=
  fun _ _ h ↦ AlgebraicGeometry.IsOpenImmersion h.left.left

/-- Scheme-level closed immersions, as a morphism property on schemes over `B`. -/
def closedImmersionSchemesOver : MorphismProperty (SchemesOver B) :=
  fun _ _ h ↦ AlgebraicGeometry.IsClosedImmersion h.left.left

/-- The Hilbert-locus inclusion is an open immersion of functors of points. -/
theorem quotHilbertι_isOpenImmersion (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) (hP : IsNumericalPolynomial P) :
    openImmersionSchemesOver.relative uliftYoneda.{u + 1}
      (quotHilbertι f F L P) :=
  sorry

/-- The Hilbert-locus inclusion is a closed immersion of functors of points. -/
theorem quotHilbertι_isClosedImmersion (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) (hP : IsNumericalPolynomial P) :
    closedImmersionSchemesOver.relative uliftYoneda.{u + 1}
      (quotHilbertι f F L P) :=
  sorry

/-- The natural transformation of Hilbert loci induced by tensoring with `L`. -/
def tensorHom_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    (quotHilbert f F L P).toFunctor ⟶
      (quotHilbert f (F ⊗ L) L (shiftPolynomial P)).toFunctor where
  app σ :=
    TypeCat.ofHom fun x ↦
      ⟨ConcreteCategory.hom ((tensorHom f F L).app σ) x.val, sorry⟩
  naturality := sorry

/-- The inverse natural transformation of Hilbert loci induced by the inverse of
tensoring with `L`. -/
def tensorInvHom_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    (quotHilbert f (F ⊗ L) L (shiftPolynomial P)).toFunctor ⟶
      (quotHilbert f F L P).toFunctor where
  app σ :=
    TypeCat.ofHom fun x ↦
      ⟨ConcreteCategory.hom ((tensorInvHom f F L).app σ) x.val, sorry⟩
  naturality := sorry

/-- Tensoring Hilbert loci commutes with the inclusions into the ambient Quot
functors. -/
theorem tensorHom_hilbert_comp_ι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : ℤ → ℤ) :
    tensorHom_hilbert f F L P ≫ quotHilbertι f (F ⊗ L) L (shiftPolynomial P) =
      quotHilbertι f F L P ≫ tensorHom f F L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
