module

public import ReasLib.AlgebraicGeometry.Scheme.SmallBoundClosed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Size
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- If `X`, `Y`, and `S` satisfy `P`, then the scheme fibre product
`pullback f g` is isomorphic to an object satisfying `P`. -/
theorem isoClosure_pullback {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {X Y S : Scheme.{u}} (hX : P X) (hY : P Y) (hS : P S) (f : X ⟶ S) (g : Y ⟶ S) :
    P.isoClosure (pullback f g) := sorry

/-- The fibre product of morphisms in the full subcategory of `P` exists. -/
theorem hasPullback {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {X Y S : P.FullSubcategory} (f : X ⟶ S) (g : Y ⟶ S) : HasPullback f g := sorry

/-- The inclusion of a small bound-closed full subcategory of schemes preserves fibre products. -/
theorem preservesPullback {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {X Y S : P.FullSubcategory} (f : X ⟶ S) (g : Y ⟶ S) :
    PreservesLimit (cospan f g) P.ι := sorry

/-- The coproduct in `Scheme` of an at most countable family of objects
satisfying `P` is isomorphic to an object satisfying `P`. -/
theorem isoClosure_sigma {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {ι : Type u} [Countable ι] (S : ι → Scheme.{u}) (hS : ∀ i, P (S i)) :
    P.isoClosure (∐ S) := sorry

/-- An at most countable coproduct of objects of the full subcategory of `P` exists. -/
theorem hasCoproduct {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {ι : Type u} [Countable ι] (S : ι → P.FullSubcategory) : HasCoproduct S := sorry

/-- The inclusion of a small bound-closed full subcategory of schemes preserves countable coproducts. -/
theorem preservesCoproduct {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {ι : Type u} [Countable ι] (S : ι → P.FullSubcategory) :
    PreservesColimit (Discrete.functor S) P.ι := sorry

/-- If `S` satisfies `P` and `f : U ⟶ S` is an open immersion, then `U` is
isomorphic to an object satisfying `P`. -/
theorem isoClosure_of_isOpenImmersion {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {U S : Scheme.{u}} (hS : P S) (f : U ⟶ S) [IsOpenImmersion f] :
    P.isoClosure U := sorry

/-- If `S` satisfies `P` and `f : T ⟶ S` is a closed immersion, then `T` is
isomorphic to an object satisfying `P`. -/
theorem isoClosure_of_isClosedImmersion {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {T S : Scheme.{u}} (hS : P S) (f : T ⟶ S) [IsClosedImmersion f] :
    P.isoClosure T := sorry

/-- If `S` satisfies `P` and `f : T ⟶ S` is of finite type, then `T` is
isomorphic to an object satisfying `P`. -/
theorem isoClosure_of_finiteType {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {T S : Scheme.{u}} (hS : P S) (f : T ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    P.isoClosure T := sorry

/-- If a scheme `S` has an open covering `U` and some `T` satisfying `P` has
`(U i).toScheme.size ≤ T.size ^ ℵ₀` for all `i` and `#ι ≤ T.size ^ ℵ₀`, then `S` is isomorphic
to an object satisfying `P`. -/
theorem isoClosure_of_isOpenCover_size_le {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {S T : Scheme.{u}} {ι : Type u} (hT : P T)
    (U : ι → S.Opens) (hU : IsOpenCover U)
    (hsize : ∀ i, (U i).toScheme.size ≤ T.size ^ ℵ₀) (hι : #ι ≤ T.size ^ ℵ₀) :
    P.isoClosure S := sorry

/-- If `S` satisfies `P` and `f : T ⟶ S` is locally of finite type, and `T`
admits an affine open covering of cardinality at most `S.size ^ ℵ₀`, then `T` is isomorphic to
an object satisfying `P`. -/
theorem isoClosure_of_locallyOfFiniteType_affine_le_power {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {T S : Scheme.{u}} (hS : P S) (f : T ⟶ S)
    [LocallyOfFiniteType f] {ι : Type u} (U : ι → T.Opens) (hU : IsOpenCover U)
    (hAff : ∀ i, IsAffineOpen (U i)) (hι : #ι ≤ S.size ^ ℵ₀) :
    P.isoClosure T := sorry

/-- If `S` satisfies `P` and `f : T ⟶ S` is locally of finite type, and `T` admits an affine open
covering of cardinality at most `|ℝ| = 2 ^ ℵ₀ = ℵ₀ ^ ℵ₀`, then `T` is isomorphic to an object
satisfying `P`. -/
theorem isoClosure_of_locallyOfFiniteType_affine_le_continuum {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {T S : Scheme.{u}} (hS : P S) (f : T ⟶ S)
    [LocallyOfFiniteType f] {ι : Type u} (U : ι → T.Opens) (hU : IsOpenCover U)
    (hAff : ∀ i, IsAffineOpen (U i)) (hι : #ι ≤ 2 ^ ℵ₀) :
    P.isoClosure T := sorry

/-- If `S` satisfies `P` and `f : T ⟶ S` is a monomorphism which is either
quasi-compact or locally of finite presentation, then `T` is isomorphic to an object
satisfying `P`. -/
theorem isoClosure_of_mono {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {T S : Scheme.{u}} (hS : P S) (f : T ⟶ S) [Mono f]
    (h : QuasiCompact f ∨ LocallyOfFinitePresentation f) :
    P.isoClosure T := sorry

/-- If `T` is an affine scheme satisfying `P` and `I` is an ideal of `Γ(T, ⊤)`,
then `Spec` of the `I`-adic completion is isomorphic to an object satisfying `P`. -/
theorem isoClosure_specAdicCompletion {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {T : Scheme.{u}} (hT : P T) [IsAffine T] (I : Ideal Γ(T, ⊤)) :
    P.isoClosure (Spec (.of (AdicCompletion I Γ(T, ⊤)))) := sorry

/-- If `T` is an affine scheme satisfying `P` and `R'` is a finite type
`Γ(T, ⊤)`-algebra, then `Spec R'` is isomorphic to an object satisfying `P`. -/
theorem isoClosure_specFiniteType {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {T : Scheme.{u}} (hT : P T) [IsAffine T] {R' : Type u} [CommRing R']
    [Algebra Γ(T, ⊤) R'] [Algebra.FiniteType Γ(T, ⊤) R'] :
    P.isoClosure (Spec (.of R')) := sorry

/-- If `T` is an affine scheme satisfying `P` and `S` is a submonoid of
`Γ(T, ⊤)`, then `Spec` of the localization is isomorphic to an object satisfying `P`. -/
theorem isoClosure_specLocalization {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {T : Scheme.{u}} (hT : P T) [IsAffine T]
    (S : Submonoid Γ(T, ⊤)) :
    P.isoClosure (Spec (.of (Localization S))) := sorry

/-- If `T` is an affine scheme satisfying `P` and `p` is a prime ideal of
`Γ(T, ⊤)`, then `Spec` of an algebraic closure of the residue field `κ(p)` is isomorphic to an
object satisfying `P`. -/
theorem isoClosure_specAlgebraicClosureResidueField {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {T : Scheme.{u}} (hT : P T) [IsAffine T]
    (p : Ideal Γ(T, ⊤)) [p.IsPrime] :
    P.isoClosure (Spec (.of (AlgebraicClosure (Ideal.ResidueField p)))) := sorry

/-- If `T` is an affine scheme satisfying `P` and `R'` is a subring of
`Γ(T, ⊤)`, then `Spec R'` is isomorphic to an object satisfying `P`. -/
theorem isoClosure_specSubring {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {T : Scheme.{u}} (hT : P T) [IsAffine T] (R' : Subring Γ(T, ⊤)) :
    P.isoClosure (Spec (.of R')) := sorry

/-- If `T` is an affine scheme satisfying `P` and `X` is of finite type over
a ring of cardinality at most `#(Γ(T, ⊤)) ^ ℵ₀`, then `X` is isomorphic to an object
satisfying `P`. -/
theorem isoClosure_finiteTypeOverCardinal {P : ObjectProperty Scheme.{u}}
    (hP : IsSmallBoundClosed P) {T : Scheme.{u}} (hT : P T) [IsAffine T]
    {A : Type u} [CommRing A] (hA : #A ≤ #(Γ(T, ⊤)) ^ ℵ₀) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f] :
    P.isoClosure X := sorry

end AlgebraicGeometry.Scheme
