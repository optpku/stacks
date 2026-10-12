/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import ReasLib.CategoryTheory.Linear.Opposite
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential operators between bundled modules

This file lifts the scalar-commutator definition of a differential operator to
`ModuleCat`.  The source and target retain their `S`-module structures, while
the morphism is linear only after restriction along `f : R →+* S`.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace ModuleCat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S) {M N L : ModuleCat.{w} S}

/-- An `R`-linear morphism between scalar restrictions of `S`-modules has
differential-operator order at most `k` when its underlying linear map has that
order relative to the retained `S`-actions. -/
@[stacks 09CI "bundled-module differential operators"]
def IsDifferentialOperatorOfOrder
    (D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N) (k : ℕ) : Prop :=
  D.hom.IsDifferentialOperatorOfOrder S k

namespace IsDifferentialOperatorOfOrder

/-- The bundled differential-operator predicate is the underlying linear-map
predicate. -/
theorem iff_hom
    (D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N) (k : ℕ) :
    IsDifferentialOperatorOfOrder f D k ↔
      D.hom.IsDifferentialOperatorOfOrder S k := sorry

/-- Forgetting the bundled modules exposes the underlying differential
operator. -/
theorem hom
    {D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N} {k : ℕ}
    (hD : IsDifferentialOperatorOfOrder f D k) :
    D.hom.IsDifferentialOperatorOfOrder S k := sorry

/-- The zero bundled morphism has every differential-operator order bound. -/
theorem zero (k : ℕ) :
    IsDifferentialOperatorOfOrder f
      (0 : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N) k := sorry

/-- The sum of two bundled differential operators with a common bound has the
same bound. -/
theorem add {D E : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder f D k)
    (hE : IsDifferentialOperatorOfOrder f E k) :
    IsDifferentialOperatorOfOrder f (D + E) k := sorry

/-- Scalar multiplication by the target ring preserves a differential-operator order bound. -/
theorem smul (s : S) {D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder f D k) :
    IsDifferentialOperatorOfOrder f (s • D) k := sorry

/-- Negation preserves the differential-operator order bound. -/
theorem neg {D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder f D k) :
    IsDifferentialOperatorOfOrder f (-D) k := sorry

/-- The identity bundled morphism is a differential operator of order zero. -/
theorem id :
    IsDifferentialOperatorOfOrder f (𝟙 ((restrictScalars f).obj M)) 0 := sorry

/-- Composing bundled differential operators adds their order bounds. -/
@[stacks 09CS "composition of bundled differential operators"]
theorem comp
    {D : (restrictScalars f).obj L ⟶ (restrictScalars f).obj M}
    {E : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N}
    {k l : ℕ} (hD : IsDifferentialOperatorOfOrder f D k)
    (hE : IsDifferentialOperatorOfOrder f E l) :
    IsDifferentialOperatorOfOrder f (D ≫ E) (k + l) := sorry

/-- An order bound implies its successor. -/
theorem le_succ
    {D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N} {k : ℕ}
    (hD : IsDifferentialOperatorOfOrder f D k) :
    IsDifferentialOperatorOfOrder f D (k + 1) := sorry

/-- A bundled differential operator has every larger order bound. -/
theorem mono
    {D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N} {k l : ℕ}
    (hD : IsDifferentialOperatorOfOrder f D k) (hkl : k ≤ l) :
    IsDifferentialOperatorOfOrder f D l := sorry

/-- Postcomposition with an `S`-linear morphism preserves the differential-operator order
bound. -/
theorem postcompose
    {D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N} {k : ℕ}
    (hD : IsDifferentialOperatorOfOrder f D k) (g : N ⟶ L) :
    IsDifferentialOperatorOfOrder f (D ≫ (restrictScalars f).map g) k := sorry

/-- Precomposition with an `S`-linear morphism preserves the differential-operator order
bound. -/
theorem precompose (g : L ⟶ M)
    {D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N} {k : ℕ}
    (hD : IsDifferentialOperatorOfOrder f D k) :
    IsDifferentialOperatorOfOrder f ((restrictScalars f).map g ≫ D) k := sorry

end IsDifferentialOperatorOfOrder

namespace DifferentialOperators

/-- The `S`-submodule of morphisms between scalar restrictions that are differential operators
of order at most `k`. -/
@[stacks 09CI "bundled operators of bounded order"]
noncomputable def submodule (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S) :
    Submodule S ((restrictScalars f).obj M ⟶ (restrictScalars f).obj N) :=
  (differentialOperatorsOrderLESubmodule R S ((restrictScalars f).obj M) k
    ((restrictScalars f).obj N)).comap ModuleCat.homLinearEquiv.toLinearMap

/-- Membership in the bundled operator submodule is the differential-operator order
predicate. -/
@[simp]
theorem mem_submodule_iff (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S)
    (D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N) :
    D ∈ submodule f M k N ↔ IsDifferentialOperatorOfOrder f D k := sorry

/-- Bundled differential operators of order at most `k` between two `S`-modules, relative to an
explicit ring homomorphism `f : R →+* S`. -/
abbrev ofOrder (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S) : Type _ :=
  submodule f M k N

/-- The module of differential operators of order at most `k`, bundled in `ModuleCat S`. -/
noncomputable abbrev module (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S) :
    ModuleCat.{w} S :=
  ModuleCat.of S (ofOrder f M k N)

/-- The category-facing bounded operators are linearly equivalent to the canonical unbundled
operator submodule.  This is the single bridge between `ModuleCat` morphisms and the reusable
linear-map API. -/
@[stacks 09CI "bundled-unbundled operator comparison"]
noncomputable def linearEquiv (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S) :
    ofOrder f M k N ≃ₗ[S]
      differentialOperatorsOrderLE R S ((restrictScalars f).obj M) k
        ((restrictScalars f).obj N) where
  toFun D := ⟨D.1.hom, D.2⟩
  invFun D := ⟨(ModuleCat.homLinearEquiv :
    ((restrictScalars f).obj M ⟶ (restrictScalars f).obj N) ≃ₗ[S]
      (((restrictScalars f).obj M) →ₗ[R] ((restrictScalars f).obj N))).symm D.1, D.2⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- The bundled/unbundled linear equivalence leaves the underlying linear map unchanged. -/
@[simp]
theorem linearEquiv_apply (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S) (D : ofOrder f M k N) :
    ((linearEquiv f M k N) D).1 = D.1.hom := sorry

/-- The restricted-scalar module morphism underlying a bundled differential operator. -/
abbrev toHom {f : R →+* S} {M N : ModuleCat.{w} S} {k : ℕ}
    (D : ofOrder f M k N) :
    (restrictScalars f).obj M ⟶ (restrictScalars f).obj N :=
  D.1

/-- Bundle a restricted-scalar morphism together with its differential-operator order bound. -/
def ofHom {f : R →+* S} {M N : ModuleCat.{w} S} {k : ℕ}
    (D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N)
    (hD : IsDifferentialOperatorOfOrder f D k) : ofOrder f M k N :=
  ⟨D, hD⟩

/-- The underlying morphism of a bundled operator satisfies its recorded order bound. -/
theorem toHom_isOfOrder {f : R →+* S} {M N : ModuleCat.{w} S} {k : ℕ}
    (D : ofOrder f M k N) :
    IsDifferentialOperatorOfOrder f (toHom D) k := sorry

/-- Bundling the underlying morphism of an operator recovers the original operator. -/
@[simp]
theorem ofHom_toHom {f : R →+* S} {M N : ModuleCat.{w} S} {k : ℕ}
    (D : ofOrder f M k N) : ofHom (toHom D) (toHom_isOfOrder D) = D := sorry

/-- Taking the underlying morphism of a freshly bundled operator recovers the input. -/
@[simp]
theorem toHom_ofHom {f : R →+* S} {M N : ModuleCat.{w} S} {k : ℕ}
    (D : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N)
    (hD : IsDifferentialOperatorOfOrder f D k) :
    toHom (ofHom D hD) = D := sorry

/-- Precomposition by an `S`-linear source morphism, bundled as an `S`-linear map between
modules of bounded differential operators. -/
@[stacks 09CK "bundled precomposition of differential operators"]
noncomputable def precomposeLinear (f : R →+* S)
    {M M' N : ModuleCat.{w} S} {k : ℕ} (g : M' ⟶ M) :
    ofOrder f M k N →ₗ[S] ofOrder f M' k N where
  toFun D := ofHom ((restrictScalars f).map g ≫ toHom D)
    (IsDifferentialOperatorOfOrder.precompose f g (toHom_isOfOrder D))
  map_add' := sorry
  map_smul' := sorry

/-- Precompose a bundled order-bounded differential operator with an `S`-linear morphism. -/
noncomputable abbrev precompose (f : R →+* S)
    {M M' N : ModuleCat.{w} S} {k : ℕ} (g : M' ⟶ M) :
    ofOrder f M k N → ofOrder f M' k N :=
  precomposeLinear f g

/-- The underlying morphism of a precomposed operator is the expected categorical
composition. -/
@[simp]
theorem toHom_precompose (f : R →+* S) {M M' N : ModuleCat.{w} S} {k : ℕ}
    (g : M' ⟶ M) (D : ofOrder f M k N) :
    toHom (precompose f g D) = (restrictScalars f).map g ≫ toHom D := sorry

/-- Precomposition is additive in a bundled differential operator. -/
theorem precompose_add (f : R →+* S) {M M' N : ModuleCat.{w} S} {k : ℕ}
    (g : M' ⟶ M) (D E : ofOrder f M k N) :
    precompose f g (D + E) = precompose f g D + precompose f g E := sorry

/-- Precomposition is linear over the target ring. -/
theorem precompose_smul (f : R →+* S) {M M' N : ModuleCat.{w} S} {k : ℕ}
    (g : M' ⟶ M) (s : S) (D : ofOrder f M k N) :
    precompose f g (s • D) = s • precompose f g D := sorry

/-- Precomposition by an identity acts identically on bundled differential operators. -/
theorem precompose_id (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ)
    (M : ModuleCat.{w} S) :
    TypeCat.ofHom (precompose (N := N) (k := k) f (𝟙 M)) =
      𝟙 (ofOrder f M k N) := sorry

/-- Precomposition reverses composition of source morphisms. -/
theorem precompose_comp (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ)
    {M L P : ModuleCat.{w} S} (g : M ⟶ L) (h : L ⟶ P) :
    TypeCat.ofHom (precompose (N := N) (k := k) f (g ≫ h)) =
      TypeCat.ofHom (precompose (N := N) (k := k) f h) ≫
        TypeCat.ofHom (precompose (N := N) (k := k) f g) := sorry

/-- The `ModuleCat` morphism induced by precomposition with an identity is the identity. -/
theorem precomposeLinear_id (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ)
    (M : ModuleCat.{w} S) :
    ModuleCat.ofHom (precomposeLinear (N := N) (k := k) f (𝟙 M)) =
      𝟙 (module f M k N) := sorry

/-- The `ModuleCat` morphisms induced by precomposition reverse composition. -/
theorem precomposeLinear_comp (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ)
    {M L P : ModuleCat.{w} S} (g : M ⟶ L) (h : L ⟶ P) :
    ModuleCat.ofHom (precomposeLinear (N := N) (k := k) f (g ≫ h)) =
      ModuleCat.ofHom (precomposeLinear (N := N) (k := k) f h) ≫
        ModuleCat.ofHom (precomposeLinear (N := N) (k := k) f g) := sorry

/-- Postcomposition with an `S`-linear morphism, transported from the canonical unbundled
differential-operator API.  The implementation pins the scalar instances because restriction
along `f` preserves the carrier definitionally, so `f` cannot be recovered from the carrier
type during instance search. -/
@[stacks 09CK "bundled postcomposition of differential operators"]
noncomputable def postcomposeLinear (f : R →+* S)
    {M N L : ModuleCat.{w} S} {k : ℕ} (g : N ⟶ L) :
    ofOrder f M k N →ₗ[S] ofOrder f M k L :=
  (linearEquiv f M k L).symm.toLinearMap.comp
    ((@differentialOperatorsOrderLE.postcompose R S
      ((restrictScalars f).obj M) ((restrictScalars f).obj N) ((restrictScalars f).obj L)
      _ _ _ _ _ (RestrictScalars.smulCommClass f M)
      _ _ _ (RestrictScalars.smulCommClass f N) (RestrictScalars.baseSmulCommClass f N) _
      _ _ _ (RestrictScalars.smulCommClass f L) (RestrictScalars.baseSmulCommClass f L) _
      (RestrictScalars.compatibleSMul f N L) g.hom k).comp
        (linearEquiv f M k N).toLinearMap)

/-- Postcompose a bundled order-bounded differential operator with an `S`-linear morphism. -/
noncomputable abbrev postcompose (f : R →+* S)
    {M N L : ModuleCat.{w} S} {k : ℕ} (g : N ⟶ L) :
    ofOrder f M k N → ofOrder f M k L :=
  postcomposeLinear f g

/-- The underlying morphism of a postcomposed operator is the expected categorical
composition. -/
@[simp]
theorem toHom_postcompose (f : R →+* S) {M N L : ModuleCat.{w} S} {k : ℕ}
    (g : N ⟶ L) (D : ofOrder f M k N) :
    toHom (postcompose f g D) = toHom D ≫ (restrictScalars f).map g := sorry

/-- Postcomposition is additive in a bundled differential operator. -/
theorem postcompose_add (f : R →+* S) {M N L : ModuleCat.{w} S} {k : ℕ}
    (g : N ⟶ L) (D E : ofOrder f M k N) :
    postcompose f g (D + E) = postcompose f g D + postcompose f g E := sorry

/-- Postcomposition is linear over the target ring. -/
theorem postcompose_smul (f : R →+* S) {M N L : ModuleCat.{w} S} {k : ℕ}
    (g : N ⟶ L) (s : S) (D : ofOrder f M k N) :
    postcompose f g (s • D) = s • postcompose f g D := sorry

/-- Postcomposition by an identity acts identically on bundled differential operators. -/
theorem postcompose_id (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S) :
    TypeCat.ofHom (postcompose (M := M) (k := k) f (𝟙 N)) = 𝟙 (ofOrder f M k N) := sorry

/-- Postcomposition of bundled differential operators respects composition in the target. -/
theorem postcompose_comp (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    {N L P : ModuleCat.{w} S} (g : N ⟶ L) (h : L ⟶ P) :
    TypeCat.ofHom (postcompose (M := M) (k := k) f (g ≫ h)) =
      TypeCat.ofHom (postcompose (M := M) (k := k) f g) ≫
        TypeCat.ofHom (postcompose (M := M) (k := k) f h) := sorry

/-- The `ModuleCat` morphism induced by postcomposition with an identity is the identity. -/
theorem postcomposeLinear_id (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    (N : ModuleCat.{w} S) :
    ModuleCat.ofHom (postcomposeLinear (M := M) (k := k) f (𝟙 N)) =
      𝟙 (module f M k N) := sorry

/-- The `ModuleCat` morphisms induced by postcomposition respect composition. -/
theorem postcomposeLinear_comp (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ)
    {N L P : ModuleCat.{w} S} (g : N ⟶ L) (h : L ⟶ P) :
    ModuleCat.ofHom (postcomposeLinear (M := M) (k := k) f (g ≫ h)) =
      ModuleCat.ofHom (postcomposeLinear (M := M) (k := k) f g) ≫
        ModuleCat.ofHom (postcomposeLinear (M := M) (k := k) f h) := sorry

/-- Simultaneous precomposition in the source and postcomposition in the target, bundled as an
`S`-linear map between modules of bounded differential operators. -/
@[stacks 09CI "bifunctoriality of bundled differential operators"]
noncomputable def bimapLinear (f : R →+* S)
    {M M' N N' : ModuleCat.{w} S} {k : ℕ} (g : M' ⟶ M) (h : N ⟶ N') :
    ofOrder f M k N →ₗ[S] ofOrder f M' k N' :=
  (postcomposeLinear (M := M') f h).comp (precomposeLinear (N := N) f g)

/-- Simultaneously precompose and postcompose a bounded differential operator. -/
noncomputable abbrev bimap (f : R →+* S)
    {M M' N N' : ModuleCat.{w} S} {k : ℕ} (g : M' ⟶ M) (h : N ⟶ N') :
    ofOrder f M k N → ofOrder f M' k N' :=
  bimapLinear f g h

/-- The underlying morphism of a bifunctorial image is ordinary composition on both sides. -/
@[simp]
theorem toHom_bimap (f : R →+* S)
    {M M' N N' : ModuleCat.{w} S} {k : ℕ} (g : M' ⟶ M) (h : N ⟶ N')
    (D : ofOrder f M k N) :
    toHom (bimap f g h D) =
      (restrictScalars f).map g ≫ toHom D ≫ (restrictScalars f).map h := sorry

/-- Acting by identities in both variables gives the identity on bounded operators. -/
@[simp]
theorem bimapLinear_id (f : R →+* S) (k : ℕ) (M N : ModuleCat.{w} S) :
    ModuleCat.ofHom (bimapLinear (k := k) f (𝟙 M) (𝟙 N)) =
      𝟙 (module f M k N) := sorry

/-- Simultaneous source and target maps compose functorially. -/
@[simp]
theorem bimapLinear_comp (f : R →+* S) (k : ℕ)
    {M M' M'' N N' N'' : ModuleCat.{w} S}
    (g : M' ⟶ M) (g' : M'' ⟶ M') (h : N ⟶ N') (h' : N' ⟶ N'') :
    ModuleCat.ofHom (bimapLinear (k := k) f (g' ≫ g) (h ≫ h')) =
      ModuleCat.ofHom (bimapLinear (k := k) f g h) ≫
        ModuleCat.ofHom (bimapLinear (k := k) f g' h') := sorry

/-- The module-valued bifunctor of bounded differential operators, contravariant in the source
and covariant in the target. -/
@[stacks 09CI "module-valued differential-operator bifunctor"]
noncomputable def moduleBifunctor (f : R →+* S) (k : ℕ) :
    (ModuleCat.{w} S)ᵒᵖ × ModuleCat.{w} S ⥤ ModuleCat.{w} S where
  obj P := module f P.1.unop k P.2
  map α := ModuleCat.ofHom (bimapLinear f α.1.unop α.2)
  map_id P := sorry
  map_comp α β := sorry

/-- The Type-valued bifunctor of bounded differential operators, contravariant in the source
and covariant in the target. -/
@[stacks 09CI "bundled differential-operator bifunctor"]
noncomputable def bifunctor (f : R →+* S) (k : ℕ) :
    (ModuleCat.{w} S)ᵒᵖ × ModuleCat.{w} S ⥤ Type _ :=
  moduleBifunctor f k ⋙ forget (ModuleCat.{w} S)

/-- The `ModuleCat S`-valued functor of order-`k` differential operators out of a fixed module. -/
@[stacks 09CI "module-valued differential-operator functor"]
noncomputable def moduleFunctor (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ) :
    ModuleCat.{w} S ⥤ ModuleCat.{w} S where
  obj N := module f M k N
  map g := ModuleCat.ofHom (postcomposeLinear f g)
  map_id N := postcomposeLinear_id f M k N
  map_comp g h := postcomposeLinear_comp f M k g h

namespace moduleFunctor

/-- The module-valued differential-operator functor preserves addition of target morphisms. -/
instance additive (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ) :
    (moduleFunctor f M k).Additive := sorry

/-- The module-valued differential-operator functor is linear over the target ring. -/
instance linear (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ) :
    Functor.Linear S (moduleFunctor f M k) := sorry

end moduleFunctor

/-- The contravariant `ModuleCat S`-valued functor of order-`k` differential operators into a
fixed target module. -/
@[stacks 09CI "contravariant module-valued differential-operator functor"]
noncomputable def sourceModuleFunctor (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ) :
    (ModuleCat.{w} S)ᵒᵖ ⥤ ModuleCat.{w} S where
  obj M := module f M.unop k N
  map g := ModuleCat.ofHom (precomposeLinear f g.unop)
  map_id M := sorry
  map_comp g h := sorry

namespace sourceModuleFunctor

/-- The source-contravariant differential-operator functor preserves addition of source
morphisms. -/
instance additive (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ) :
    (sourceModuleFunctor f N k).Additive := sorry

/-- The source-contravariant differential-operator functor is linear over the target ring. -/
instance linear (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ) :
    Functor.Linear S (sourceModuleFunctor f N k) := sorry

end sourceModuleFunctor

/-- The covariant functor of order-`k` differential operators out of a bundled `S`-module. -/
@[stacks 09CI "bundled differential-operator functor"]
noncomputable def functor (f : R →+* S) (M : ModuleCat.{w} S) (k : ℕ) :
    ModuleCat.{w} S ⥤ Type _ :=
  moduleFunctor f M k ⋙ forget (ModuleCat.{w} S)

/-- The contravariant Type-valued functor of order-`k` differential operators into a fixed
bundled `S`-module. -/
@[stacks 09CI "contravariant bundled differential-operator functor"]
noncomputable def sourceFunctor (f : R →+* S) (N : ModuleCat.{w} S) (k : ℕ) :
    (ModuleCat.{w} S)ᵒᵖ ⥤ Type _ :=
  sourceModuleFunctor f N k ⋙ forget (ModuleCat.{w} S)

end DifferentialOperators

end ModuleCat
