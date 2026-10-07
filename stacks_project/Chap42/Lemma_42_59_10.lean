module

public import stacks_project.Chap42.Lemma_42_59_10_Excess
public import stacks_project.Chap42.Lemma_42_59_10_Pullback
public import stacks_project.Chap42.Lemma_42_59_5
public import stacks_project.Chap42.Lemma_42_35_4_OpenRestriction
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom.NaiveCotangent.BaseChange
open Scheme.Hom Scheme.Hom.VirtualNormalBundle

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Lemma 42.59.10 (1): for a cartesian square of schemes whose vertical maps are local
complete intersections, `excessConormal hpb` is finite locally free. -/
@[stacks 0FV9, instance]
instance excessConormal_isFiniteLocallyFree
    {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'] :
    (excessConormal hpb).IsFiniteLocallyFree := sorry

/-- Lemma 42.59.10 (2): in Situation 42.7.1, for a cartesian square of schemes locally of
finite type over `S` whose vertical maps are local complete intersections, if the Gysin
map exists for `f` then it exists for `f'`. -/
@[stacks 0FV9]
theorem hasGysinMap_of_isPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [LocallyOfFiniteType g.left]
    (square : IsPullback g'.left f'.left f.left g.left)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'.left]
    (hf : HasGysinMap f) : HasGysinMap f' := sorry

/-- The Gysin class of an immersion-smooth factorization, formed from the rank-`r` canonical
normal-bundle class and the flat pullback of relative dimension `t`. -/
noncomputable def canonicalGysinClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (h : P ⟶ Y) (hi : IsImmersion i.left)
    [IsClosedImmersion i.left] (hh : Smooth h.left) (hfac : i ≫ h = f)
    (V : Scheme.Hom.VirtualNormalBundle i.left)
    (D : ClosedSpecialization δ X.hom P.hom i.left (Over.w i) V)
    (r t : ℕ) [Scheme.Hom.RelativeDimension h.left t] :
    BivariantClass δ f ((r : ℤ) + (-(t : ℤ))) :=
  bivariantGysinClassOfFactorization δ X Y f P i h hi hh hfac
    (overHom_eq_over i ▸
      globalClassOfRank δ X.hom P.hom i.left (Over.w i) V D r)
    (flatPullback δ h t)

/-- `canonicalGysinClass` is the Gysin class of the supplied factorization. -/
theorem canonicalGysinClass_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (h : P ⟶ Y) (hi : IsImmersion i.left)
    [IsClosedImmersion i.left] (hh : Smooth h.left) (hfac : i ≫ h = f)
    (V : Scheme.Hom.VirtualNormalBundle i.left)
    (D : ClosedSpecialization δ X.hom P.hom i.left (Over.w i) V)
    (r t : ℕ) [Scheme.Hom.RelativeDimension h.left t] :
    canonicalGysinClass δ f i h hi hh hfac V D r t =
      bivariantGysinClassOfFactorization δ X Y f P i h hi hh hfac
        (overHom_eq_over i ▸
          globalClassOfRank δ X.hom P.hom i.left (Over.w i) V D r)
        (flatPullback δ h t) := sorry

/-- The dual excess conormal sheaf of an lci cartesian square is finite locally free. -/
instance excessConormalDual_isFiniteLocallyFree
    {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'] :
    (excessConormalDual hpb).IsFiniteLocallyFree :=
  (inferInstance : (Scheme.Modules.dual (excessConormal hpb)).IsFiniteLocallyFree)

/-- The virtual normal bundle whose module is the normal sheaf of an immersion, without a
global rank hypothesis, using a chosen bidual identification with the conormal sheaf. -/
noncomputable def regularImmersionNormalBundle
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.normalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    VirtualNormalBundle i :=
  ofSurjection i (Scheme.Hom.normalSheaf i) inferInstance e.hom inferInstance

/-- The normal sheaf of the induced immersion in a smooth factorization of the primed
lci morphism is finite locally free over a locally Noetherian target. -/
instance gysinBaseChangeImmersion_normalSheaf_isFiniteLocallyFree
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f)
    [IsRegularImmersion i.left] [LocallyOfFiniteType Y'.hom]
    [Smooth h.left] [LocallyOfType RingHom.IsLocalCompleteIntersection f'.left] :
    (Scheme.Hom.normalSheaf
      (gysinBaseChangeImmersion square i h hfac).left).IsFiniteLocallyFree := sorry

/-- The module of `regularImmersionNormalBundle` is the normal sheaf. -/
theorem regularImmersionNormalBundle_module
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.normalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    (regularImmersionNormalBundle i e).module = Scheme.Hom.normalSheaf i := sorry

/-- The quotient map of `regularImmersionNormalBundle` is the chosen bidual identification. -/
theorem regularImmersionNormalBundle_map
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.normalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    (regularImmersionNormalBundle i e).map = e.hom := sorry

/-- The rank-`r` open of the dual excess conormal sheaf of a cartesian square. -/
abbrev excessDualRankOpen
    {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (r : ℕ)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'] :
    X'.Opens :=
  (Scheme.Modules.rankClopen (excessConormalDual hpb) r).toOpens

/-- `excessDualRankOpen` is the rank-`r` clopen of `excessConormalDual`. -/
theorem excessDualRankOpen_eq
    {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (r : ℕ)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'] :
    excessDualRankOpen hpb r =
      (Scheme.Modules.rankClopen (excessConormalDual hpb) r).toOpens := sorry

/-- Rank loci of a finite locally free sheaf on the source lie in the preimage of the
top open of the target. -/
theorem rankClopen_le_preimage_top
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (E : X.left.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    (Scheme.Modules.rankClopen E r).toOpens ≤ f.left ⁻¹ᵁ (⊤ : Y.left.Opens) := sorry

/-- Rank loci are preserved by the identity morphism of an `S`-scheme. -/
theorem rankClopen_le_id_preimage
    {S : Scheme.{u}} {X : Over S}
    (E : X.left.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    (Scheme.Modules.rankClopen E r).toOpens ≤
      (𝟙 X : X ⟶ X).left ⁻¹ᵁ (Scheme.Modules.rankClopen E r).toOpens := sorry

/-- The top Chern class of a finite locally free sheaf on its rank-`r` locus. -/
noncomputable def topChernRankComponent
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    (E : X.left.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    ChernClass.RankComponentClass δ X.hom E r r :=
  ChernClass.rankComponent δ X.hom E r ⟨r, Nat.lt_succ_self r⟩

/-- `topChernRankComponent` is the canonical rank-`r` Chern component. -/
theorem topChernRankComponent_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    (E : X.left.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    topChernRankComponent δ E r =
      ChernClass.rankComponent δ X.hom E r ⟨r, Nat.lt_succ_self r⟩ := sorry

/-- The Gysin degree identity `r + (r' - t) = c - t` obtained from `r + r' = c`. -/
theorem gysin_excess_degree {r r' t c : ℕ} (hr : r + r' = c) :
    ((r : ℤ) + ((r' : ℤ) + (-(t : ℤ)))) = (c : ℤ) + (-(t : ℤ)) := sorry

/-- Transport a homogeneous bivariant class along `Category.id_comp`. -/
noncomputable def idCompCast
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (c : BivariantClass δ (𝟙 X ≫ f) p) :
    BivariantClass δ f p :=
  Category.id_comp f ▸ c

/-- `idCompCast` is transport along `Category.id_comp`. -/
theorem idCompCast_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (c : BivariantClass δ (𝟙 X ≫ f) p) :
    idCompCast δ c = Category.id_comp f ▸ c := sorry

/-- Lemma 42.59.10 (3): in Situation 42.7.1, for a cartesian square of schemes locally of
finite type over `S` whose vertical maps are local complete intersections, if `f` factors as
a closed regular immersion followed by a smooth morphism, then on every rank locus of the
dual excess conormal sheaf `C^∨` one has `res(f^!) = c_top(C^∨) ∘ (f')^!` in
`A^*(X' ⟶ Y')`. Here `f^!` is the canonical Gysin class of the given factorization at the
constant conormal rank `c`, `(f')^!` is the canonical Gysin class of the induced
factorization of `f'` with virtual normal bundle `N' = C_{X'/P'}^∨`, and `c_top(C^∨)` is
the rank-`r` Chern component of `excessConormalDual`, under the degree identity
`r + r' = c`. -/
@[stacks 0FV9]
theorem restrict_gysin_eq_topChern_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [LocallyOfFiniteType g.left]
    (square : IsPullback g'.left f'.left f.left g.left)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (h : P ⟶ Y) (hi : IsImmersion i.left)
    [IsClosedImmersion i.left] [IsRegularImmersion i.left]
    (hh : Smooth h.left) (hfac : i ≫ h = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension h.left t]
    (c : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (D : ClosedSpecialization δ X.hom P.hom i.left
      (Over.w i) (ofNormalSheaf i.left c e))
    (e' : Scheme.Modules.dual
        (Scheme.Hom.normalSheaf (gysinBaseChangeImmersion square i h hfac).left) ≅
      Scheme.Hom.conormalSheaf (gysinBaseChangeImmersion square i h hfac).left)
    (D' : ClosedSpecialization δ X'.hom
      (OpenRestriction.baseChange h g).hom
      (gysinBaseChangeImmersion square i h hfac).left
      (Over.w (gysinBaseChangeImmersion square i h hfac))
      (regularImmersionNormalBundle
        (gysinBaseChangeImmersion square i h hfac).left e'))
    (r r' : ℕ) (hr : r + r' = c) :
    OpenRestriction.restrict δ f' ((c : ℤ) + (-(t : ℤ)))
        (excessDualRankOpen square r) ⊤
        (rankClopen_le_preimage_top f' (excessConormalDual square) r)
        (restrict δ g' f' g square ((c : ℤ) + (-(t : ℤ)))
          (canonicalGysinClass δ f i h hi hh hfac
            (ofNormalSheaf i.left c e) D c t)) =
      Nonnegative.castGrading δ (gysin_excess_degree hr)
        (idCompCast δ
          (comp δ
            (𝟙 (OpenRestriction.over X'
              (excessDualRankOpen square r)))
            (OpenRestriction.hom f'
              (excessDualRankOpen square r) ⊤
              (rankClopen_le_preimage_top f' (excessConormalDual square) r))
            (ChernClass.restrictComponent δ
              (OpenRestriction.hom (𝟙 X')
                (excessDualRankOpen square r)
                (excessDualRankOpen square r)
                (rankClopen_le_id_preimage (excessConormalDual square) r))
              r (topChernRankComponent δ (excessConormalDual square) r))
            (OpenRestriction.restrict δ f' ((r' : ℤ) + (-(t : ℤ)))
              (excessDualRankOpen square r) ⊤
              (rankClopen_le_preimage_top f' (excessConormalDual square) r)
              (canonicalGysinClass δ f'
                (gysinBaseChangeImmersion square i h hfac)
                (OpenRestriction.baseChangeToTarget h g)
                (gysinBaseChangeImmersion_isImmersion square i h hfac)
                (gysinBaseChangeToTarget_smooth h g)
                (gysinBaseChange_fac square i h hfac)
                (regularImmersionNormalBundle
                  (gysinBaseChangeImmersion square i h hfac).left e')
                D' r' t)))) := sorry

end AlgebraicGeometry.BivariantClass
