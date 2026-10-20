module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Section
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.OpenImmersion
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass
public import stacks_project.Chap42.Situation_42_7_1

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

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

/-- The canonical isomorphism identifying `Over.mk X.hom` with `X`. -/
def overMkIso {S : Scheme.{u}} (X : Over S) : Over.mk X.hom ≅ X :=
  Over.isoMk (Iso.refl X.left) (Category.id_comp X.hom)

/-- `overMkIso` is the identity isomorphism on underlying schemes. -/
theorem overMkIso_left {S : Scheme.{u}} (X : Over S) :
    (overMkIso X).hom.left = 𝟙 X.left := sorry

/-- The virtual-normal packaging of an over-morphism is the conjugate of that morphism by the
canonical `Over.mk` isomorphisms. -/
theorem overHom_eq_overMkIso_conj {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) :
    overHom X.hom P.hom s.left (Over.w s) =
      (overMkIso X).hom ≫ s ≫ (overMkIso P).inv := sorry

/-- The canonical `Over.mk` isomorphisms form a pullback square against an over-morphism and
its virtual-normal packaging. -/
theorem overMkIso_conj_isPullback {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) :
    IsPullback (overMkIso X).inv.left s.left
      (overHom X.hom P.hom s.left (Over.w s)).left (overMkIso P).inv.left := sorry

/-- The canonical isomorphism `Over.mk X.hom ≅ X` forms a pullback square of identity
morphisms. -/
theorem overMkIso_id_isPullback {S : Scheme.{u}} (X : Over S) :
    IsPullback (overMkIso X).inv.left (Over.Hom.left (𝟙 X))
      (Over.Hom.left (𝟙 (Over.mk X.hom))) (overMkIso X).inv.left := sorry

/-- Integer grading identity used when a degree-zero class caps a cycle of dimension `n`. -/
theorem gysin_section_cap_degree (n : ℤ) : n - 0 = n := sorry

/-- The closed coborder factor of a section, as a morphism over `S`. -/
noncomputable def sectionCoborderClosed
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    Over.mk X.hom ⟶ Over.mk (s.left.coborderRange.ι ≫ P.hom) :=
  overHom X.hom (s.left.coborderRange.ι ≫ P.hom) s.left.liftCoborder
    (factorization_over X.hom P.hom s.left s.w
      s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)

/-- `sectionCoborderClosed` is the virtual-normal `overHom` of the coborder closed immersion. -/
theorem sectionCoborderClosed_def
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    sectionCoborderClosed s =
      overHom X.hom (s.left.coborderRange.ι ≫ P.hom) s.left.liftCoborder
        (factorization_over X.hom P.hom s.left s.w
          s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι) := sorry

/-- The open coborder factor of a section, as a morphism over `S`. -/
noncomputable def sectionCoborderOpen
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    Over.mk (s.left.coborderRange.ι ≫ P.hom) ⟶ Over.mk P.hom :=
  overHom (s.left.coborderRange.ι ≫ P.hom) P.hom s.left.coborderRange.ι rfl

/-- `sectionCoborderOpen` is the virtual-normal `overHom` of the coborder open immersion. -/
theorem sectionCoborderOpen_def
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    sectionCoborderOpen s =
      overHom (s.left.coborderRange.ι ≫ P.hom) P.hom s.left.coborderRange.ι rfl := sorry

/-- The underlying scheme morphism of `sectionCoborderOpen` is an open immersion. -/
instance sectionCoborderOpen_isOpenImmersion
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    IsOpenImmersion (sectionCoborderOpen s).left := sorry

/-- The coborder closed-open factorization of a section recovers the virtual-normal packaging of
the section. -/
theorem gysinSection_factorization
    {S : Scheme.{u}} {X P : Over S} (s : X ⟶ P) [IsImmersion s.left] :
    sectionCoborderClosed s ≫ sectionCoborderOpen s =
      overHom X.hom P.hom s.left s.w := sorry

/-- The canonical `Over.mk` isomorphisms form a pullback square against a section and its
coborder factorization. -/
theorem sectionCoborder_conj_isPullback {S : Scheme.{u}} {X P : Over S}
    (s : X ⟶ P) [IsImmersion s.left] :
    IsPullback (overMkIso X).inv.left s.left
      (sectionCoborderClosed s ≫ sectionCoborderOpen s).left
      (overMkIso P).inv.left := sorry

/-- The Gysin class of a section as a class of `s : X ⟶ P`: coborder composition on `Over.mk`,
conjugated along `overMkIso`. -/
noncomputable def gysinSection
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [IsImmersion s.left] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedSpecialization δ X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder) :
    BivariantClass δ s (r : ℤ) :=
  Nonnegative.castGrading δ
      ((congrArg ((r : ℤ) + ·) neg_zero).trans (add_zero (r : ℤ)))
    (restrict δ (overMkIso X).inv s (overMkIso P).inv
      (sectionCoborder_conj_isPullback s) ((r : ℤ) + (-(0 : ℤ)))
      (comp δ (sectionCoborderClosed s) (sectionCoborderOpen s)
        (globalClassOfRank δ X.hom (s.left.coborderRange.ι ≫ P.hom)
          s.left.liftCoborder
          (factorization_over X.hom P.hom s.left s.w
            s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
          (ofNormalSheaf s.left r e).toCoborder D r)
        (flatPullback δ (sectionCoborderOpen s) 0)))

/-- `gysinSection` is the degree-`r` conjugate of the coborder closed class of the normal sheaf
composed with degree-zero open pullback. -/
theorem gysinSection_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (s : X ⟶ P) [IsImmersion s.left] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedSpecialization δ X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder) :
    gysinSection δ s r e D =
      Nonnegative.castGrading δ
          ((congrArg ((r : ℤ) + ·) neg_zero).trans (add_zero (r : ℤ)))
        (restrict δ (overMkIso X).inv s (overMkIso P).inv
          (sectionCoborder_conj_isPullback s) ((r : ℤ) + (-(0 : ℤ)))
          (comp δ (sectionCoborderClosed s) (sectionCoborderOpen s)
            (globalClassOfRank δ X.hom (s.left.coborderRange.ι ≫ P.hom)
              s.left.liftCoborder
              (factorization_over X.hom P.hom s.left s.w
                s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
              (ofNormalSheaf s.left r e).toCoborder D r)
            (flatPullback δ (sectionCoborderOpen s) 0))) := sorry

/-- The degree-zero identity class of `𝟙 X`, obtained by conjugating `ChowCohomology.one` along
`overMkIso X`. -/
noncomputable def oneOver
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] :
    BivariantClass δ (𝟙 X) 0 :=
  restrict δ (overMkIso X).inv (𝟙 X) (overMkIso X).inv
    (overMkIso_id_isPullback X) 0 (ChowCohomology.one δ X.hom)

/-- `oneOver` is restriction of `ChowCohomology.one` along the canonical `Over.mk` isomorphism. -/
theorem oneOver_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] :
    oneOver δ X =
      restrict δ (overMkIso X).inv (𝟙 X) (overMkIso X).inv
        (overMkIso_id_isPullback X) 0
        (ChowCohomology.one δ X.hom) := sorry

/-- The Chow class of a closed subscheme of an object of `Over S`, in relative dimension `n`. -/
noncomputable def closedSubschemeChowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] (Z : X.left.IdealSheafData) (n : ℤ)
    (hZ : X.hom.closedSubschemeDeltaDimension δ Z ≤ (n : EInt)) :
    RelativeChow δ X n :=
  @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
    (X.hom.relativeDimensionFunction δ) inferInstance n
    (X.hom.closedSubschemeCycle δ Z n hZ)

/-- `closedSubschemeChowClass` is the Chow class of the associated closed-subscheme cycle. -/
theorem closedSubschemeChowClass_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] (Z : X.left.IdealSheafData) (n : ℤ)
    (hZ : X.hom.closedSubschemeDeltaDimension δ Z ≤ (n : EInt)) :
    closedSubschemeChowClass δ Z n hZ =
      @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance n
        (X.hom.closedSubschemeCycle δ Z n hZ) := sorry

/-- Lemma 42.59.2 (1): in Situation 42.7.1, a section of a smooth morphism of schemes locally of
finite type over `S` is a regular immersion. -/
@[stacks 0FF1]
theorem section_isRegularImmersion
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X) :
    IsRegularImmersion s.left := sorry

/-- Lemma 42.59.2 (2): in Situation 42.7.1, if `p` is smooth of relative dimension `r` and `s` is a
section of `p`, then `1 = s^! ∘ p^*` in `A^0(X)`, where `s^!` is the virtual-normal Gysin class of
the normal sheaf of `s` and `p^*` is the flat-pullback class of Lemma 42.33.2. -/
@[stacks 0FF1]
theorem gysin_section_comp_flatPullback_eq_one
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (r : ℕ) [Scheme.Hom.RelativeDimension p.left r]
    (s : X ⟶ P) [IsImmersion s.left] (hs : s ≫ p = 𝟙 X)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedSpecialization δ X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder) :
    Nonnegative.castGrading δ (add_neg_cancel (r : ℤ))
        (hs ▸ comp δ s p (gysinSection δ s r e D) (flatPullback δ p r)) =
      oneOver δ X := sorry

/-- Capping the identity `s^! ∘ p^*` against the Chow class of an integral closed subscheme of
`X` recovers that class. -/
theorem gysin_section_comp_flatPullback_cap_fundamental
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (r : ℕ) [Scheme.Hom.RelativeDimension p.left r]
    (s : X ⟶ P) [IsImmersion s.left] (hs : s ≫ p = 𝟙 X)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedSpecialization δ X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder)
    (Z : X.left.IdealSheafData) [IsIntegral Z.subscheme] (n : ℤ)
    (hZ : X.hom.closedSubschemeDeltaDimension δ Z = (n : EInt)) :
    gysin_section_cap_degree n ▸
        (Nonnegative.castGrading δ (add_neg_cancel (r : ℤ))
            (hs ▸ comp δ s p (gysinSection δ s r e D) (flatPullback δ p r))).cap
          (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd n
          (closedSubschemeChowClass δ Z n (le_of_eq hZ)) =
      closedSubschemeChowClass δ Z n (le_of_eq hZ) := sorry

end AlgebraicGeometry.BivariantClass

