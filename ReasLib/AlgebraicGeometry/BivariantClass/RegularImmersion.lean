module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.NormalSheaf
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.OpenImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- An open immersion has relative dimension zero. -/
instance instRelativeDimensionZeroOfIsOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    RelativeDimension f 0 :=
  relativeDimension_zero_of_isOpenImmersion f

/-- The underlying scheme morphism of `overHom` for an open immersion is an open immersion. -/
instance overHom_isOpenImmersion
    {S U X : Scheme.{u}} (q : U ⟶ S) (p : X ⟶ S) (k : U ⟶ X)
    (hk : k ≫ p = q) [IsOpenImmersion k] :
    IsOpenImmersion (overHom q p k hk).left := sorry

/-- The conormal sheaf of a regular immersion is finite locally free. -/
instance conormalSheaf_isFiniteLocallyFree_of_isRegularImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i] :
    (conormalSheaf i).IsFiniteLocallyFree := sorry

/-- The normal sheaf of a regular immersion is finite locally free. -/
instance normalSheaf_isFiniteLocallyFree_of_isRegularImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i] :
    (normalSheaf i).IsFiniteLocallyFree := sorry

/-- The virtual normal bundle whose module is the normal sheaf, via a chosen bidual
identification with the conormal sheaf. -/
noncomputable def normalSheafBundle {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.normalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    VirtualNormalBundle i :=
  ofSurjection i (Scheme.Hom.normalSheaf i) inferInstance e.hom inferInstance

/-- The module of `normalSheafBundle` is the normal sheaf. -/
theorem normalSheafBundle_module {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.normalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    (normalSheafBundle i e).module = Scheme.Hom.normalSheaf i := sorry

/-- The closed coborder factor of an immersion, as a morphism over `S`. -/
noncomputable def coborderClosed
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsImmersion f.left] :
    Over.mk X.hom ⟶ Over.mk (f.left.coborderRange.ι ≫ Y.hom) :=
  overHom X.hom (f.left.coborderRange.ι ≫ Y.hom) f.left.liftCoborder
    (factorization_over X.hom Y.hom f.left f.w
      f.left.liftCoborder f.left.coborderRange.ι f.left.liftCoborder_ι)

/-- `coborderClosed` is the virtual-normal `overHom` of the coborder closed immersion. -/
theorem coborderClosed_def
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsImmersion f.left] :
    coborderClosed f =
      overHom X.hom (f.left.coborderRange.ι ≫ Y.hom) f.left.liftCoborder
        (factorization_over X.hom Y.hom f.left f.w
          f.left.liftCoborder f.left.coborderRange.ι f.left.liftCoborder_ι) := sorry

/-- The open coborder factor of an immersion, as a morphism over `S`. -/
noncomputable abbrev coborderOpen
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsImmersion f.left] :
    Over.mk (f.left.coborderRange.ι ≫ Y.hom) ⟶ Over.mk Y.hom :=
  overHom (f.left.coborderRange.ι ≫ Y.hom) Y.hom f.left.coborderRange.ι rfl

/-- `coborderOpen` is the virtual-normal `overHom` of the coborder open immersion. -/
theorem coborderOpen_def
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsImmersion f.left] :
    coborderOpen f =
      overHom (f.left.coborderRange.ι ≫ Y.hom) Y.hom f.left.coborderRange.ι rfl := sorry

/-- The coborder closed-open factorization recovers the virtual-normal packaging of the
immersion. -/
theorem coborder_factorization
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [immersion : IsImmersion f.left] :
    coborderClosed f ≫ coborderOpen f = overHom X.hom Y.hom f.left f.w := sorry

/-- Integer grading identity comparing a nonnegative degree with the degree-zero open-immersion
flat pullback. -/
theorem gysin_open_degree (n : ℕ) : (n : ℤ) + (-(0 : ℤ)) = (n : ℤ) := sorry

/-- Integer grading identity comparing the Gysin composition degree `(r : ℤ) + (s : ℤ)` with
the composite rank `(r + s : ℤ)`. -/
theorem gysin_comp_degree (r s : ℕ) : (r : ℤ) + (s : ℤ) = ((r + s) : ℤ) := sorry

/-- The degree-`n` Gysin class of a regular immersion, formed by the coborder closed class of
the normal sheaf and degree-zero open pullback along the coborder range. -/
noncomputable def gysinImmersion
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [regular : IsRegularImmersion f.left]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf f.left) ≅
      Scheme.Hom.conormalSheaf f.left)
    (D : ClosedDeformation X.hom (f.left.coborderRange.ι ≫ Y.hom)
      f.left.liftCoborder
      (factorization_over X.hom Y.hom f.left f.w
        f.left.liftCoborder f.left.coborderRange.ι f.left.liftCoborder_ι)
      (normalSheafBundle f.left e).toCoborder)
    (n : ℕ) :
    BivariantClass δ (coborderClosed f ≫ coborderOpen f) ((n : ℤ) + (-(0 : ℤ))) :=
  comp δ (coborderClosed f) (coborderOpen f)
    (globalClassOfRank δ X.hom (f.left.coborderRange.ι ≫ Y.hom)
      f.left.liftCoborder
      (factorization_over X.hom Y.hom f.left f.w
        f.left.liftCoborder f.left.coborderRange.ι f.left.liftCoborder_ι)
      (normalSheafBundle f.left e).toCoborder D n)
    (flatPullback δ (coborderOpen f) 0)

/-- `gysinImmersion` is the coborder composition of `globalClassOfRank` with degree-zero open
pullback. -/
theorem gysinImmersion_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsRegularImmersion f.left]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf f.left) ≅
      Scheme.Hom.conormalSheaf f.left)
    (D : ClosedDeformation X.hom (f.left.coborderRange.ι ≫ Y.hom)
      f.left.liftCoborder
      (factorization_over X.hom Y.hom f.left f.w
        f.left.liftCoborder f.left.coborderRange.ι f.left.liftCoborder_ι)
      (normalSheafBundle f.left e).toCoborder)
    (n : ℕ) :
    gysinImmersion δ f e D n =
      comp δ (coborderClosed f) (coborderOpen f)
        (globalClassOfRank δ X.hom (f.left.coborderRange.ι ≫ Y.hom)
          f.left.liftCoborder
          (factorization_over X.hom Y.hom f.left f.w
            f.left.liftCoborder f.left.coborderRange.ι f.left.liftCoborder_ι)
          (normalSheafBundle f.left e).toCoborder D n)
        (flatPullback δ (coborderOpen f) 0) := sorry

/-- For closed regular immersions of globally constant conormal ranks, the Gysin composition
identity is the homogeneous comparison of `globalClassOfRank` classes. -/
theorem gysin_comp_closed
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i.left] [IsRegularImmersion i.left]
    [IsClosedImmersion j.left] [IsRegularImmersion j.left]
    (r s : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i.left)]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank s (Scheme.Hom.conormalSheaf j.left)]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (r + s)
      (Scheme.Hom.conormalSheaf (i.left ≫ j.left))]
    (ei : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (ej : Scheme.Modules.dual (Scheme.Hom.normalSheaf j.left) ≅
      Scheme.Hom.conormalSheaf j.left)
    (eij : Scheme.Modules.dual (Scheme.Hom.normalSheaf (i.left ≫ j.left)) ≅
      Scheme.Hom.conormalSheaf (i.left ≫ j.left))
    (Di : ClosedDeformation X.hom Y.hom i.left (Over.w i)
      (ofNormalSheaf i.left r ei))
    (Dj : ClosedDeformation Y.hom Z.hom j.left (Over.w j)
      (ofNormalSheaf j.left s ej))
    (Dij : ClosedDeformation X.hom Z.hom (i.left ≫ j.left) (Over.w (i ≫ j))
      (ofNormalSheaf (i.left ≫ j.left) (r + s) eij)) :
    Nonnegative.castGrading δ (gysin_comp_degree r s)
        (comp δ i j
          (overHom_eq_over i ▸
            globalClassOfRank δ X.hom Y.hom i.left (Over.w i)
              (ofNormalSheaf i.left r ei) Di r)
          (overHom_eq_over j ▸
            globalClassOfRank δ Y.hom Z.hom j.left (Over.w j)
              (ofNormalSheaf j.left s ej) Dj s)) =
      overHom_eq_over (i ≫ j) ▸
        globalClassOfRank δ X.hom Z.hom (i.left ≫ j.left) (Over.w (i ≫ j))
          (ofNormalSheaf (i.left ≫ j.left) (r + s) eij) Dij (r + s) := sorry

/-- The completed normal-sheaf Gysin class of a composite of regular immersions equals
the convolution of their completed Gysin classes in every nonnegative degree. -/
theorem gysin_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsRegularImmersion i.left] [IsRegularImmersion j.left]
    (ei : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (ej : Scheme.Modules.dual (Scheme.Hom.normalSheaf j.left) ≅
      Scheme.Hom.conormalSheaf j.left)
    (eij : Scheme.Modules.dual (Scheme.Hom.normalSheaf (i.left ≫ j.left)) ≅
      Scheme.Hom.conormalSheaf (i.left ≫ j.left))
    (Di : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ Y.hom)
      i.left.liftCoborder
      (factorization_over X.hom Y.hom i.left i.w
        i.left.liftCoborder i.left.coborderRange.ι i.left.liftCoborder_ι)
      (normalSheafBundle i.left ei).toCoborder)
    (Dj : ClosedDeformation Y.hom (j.left.coborderRange.ι ≫ Z.hom)
      j.left.liftCoborder
      (factorization_over Y.hom Z.hom j.left j.w
        j.left.liftCoborder j.left.coborderRange.ι j.left.liftCoborder_ι)
      (normalSheafBundle j.left ej).toCoborder)
    (Dij : ClosedDeformation X.hom
      ((i.left ≫ j.left).coborderRange.ι ≫ Z.hom)
      (i.left ≫ j.left).liftCoborder
      (factorization_over X.hom Z.hom (i.left ≫ j.left) (i ≫ j).w
        (i.left ≫ j.left).liftCoborder (i.left ≫ j.left).coborderRange.ι
        (i.left ≫ j.left).liftCoborder_ι)
      (normalSheafBundle (i.left ≫ j.left) eij).toCoborder)
    (n : ℕ) :
    @Finset.sum
        {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}
        (BivariantClass δ (i ≫ j) (n : ℤ))
        (pointwiseAddCommGroup δ (i ≫ j) (n : ℤ)).toAddCommMonoid
        Finset.univ
        (fun ij ↦
          Nonnegative.castGrading δ (Nonnegative.antidiagonalDegree n ij)
            (comp δ i j
              (overHom_eq_over i ▸ coborder_factorization i ▸
                Nonnegative.castGrading δ (gysin_open_degree ij.1.1)
                  (gysinImmersion δ i ei Di ij.1.1))
              (overHom_eq_over j ▸ coborder_factorization j ▸
                Nonnegative.castGrading δ (gysin_open_degree ij.1.2)
                  (gysinImmersion δ j ej Dj ij.1.2)))) =
      overHom_eq_over (i ≫ j) ▸ coborder_factorization (i ≫ j)
        (immersion := inferInstanceAs (IsImmersion (i.left ≫ j.left))) ▸
        Nonnegative.castGrading δ (gysin_open_degree n)
          (gysinImmersion δ (i ≫ j)
            (regular := inferInstanceAs (IsRegularImmersion (i.left ≫ j.left))) eij Dij n) := sorry

end AlgebraicGeometry.BivariantClass
