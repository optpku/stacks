module

public import stacks_project.Chap82.Definition_82_26_1_Bivariant
public import stacks_project.Chap82.Remark_82_22_3_Pullback

/-!
# Zero-scheme Gysin as a bivariant class

In Situation 82.2.1, a Definition 82.22.1 triple `(L, s, i : D ⟶ X)` of a
good algebraic space over `B` determines a degree-`1` bivariant class of
`i = zeroSchemeι L s` whose cap maps are refined Gysin along the pulled-back
section, transported to the displayed zero-scheme fibre `D'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BivariantClass

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- The canonical comparison from the zero scheme of the pulled-back section
to the source of a displayed cartesian square for `zeroSchemeι L s`. -/
noncomputable def gysinBaseChangeIso {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) :
    (zeroScheme ((Modules.pullback g).obj L)
        (Modules.sectionsPullback g L s)).X ≅ D' :=
  (zeroSchemePullbackSquare g L s).isoIsPullback _ _ square.flip

/-- The Gysin base-change isomorphism respects structure morphisms over `B`. -/
theorem gysinBaseChangeIso_hom_comp_structure {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) :
    (gysinBaseChangeIso L s j i' g square).hom ≫
        (j ≫ zeroSchemeι L s ≫ pX) =
      zeroSchemeι ((Modules.pullback g).obj L)
          (Modules.sectionsPullback g L s) ≫ g ≫ pX :=
  sorry

/-- Chow-level refined Gysin along a cartesian square whose pulled-back
module is already known to be invertible. -/
noncomputable def chowGysin_isPullback.ofInvertible {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    Hom.chowGroup (g ≫ pX) δ k →+
      Hom.chowGroup (j ≫ zeroSchemeι L s ≫ pX) δ (k - 1) :=
  (Hom.properPushforward δ
      (zeroSchemeι ((Modules.pullback g).obj L)
        (Modules.sectionsPullback g L s) ≫ g ≫ pX)
      (j ≫ zeroSchemeι L s ≫ pX)
      (gysinBaseChangeIso L s j i' g square).hom
      (gysinBaseChangeIso_hom_comp_structure pX L s j i' g square) (k - 1)).comp
    ((Hom.chowGysin δ (g ≫ pX) ((Modules.pullback g).obj L)
        (Modules.sectionsPullback g L s) (k - 1)).comp
      (ChowCohomology.castChowGroup δ (g ≫ pX) (sub_add_cancel k 1).symm))

/-- Unfolding of `chowGysin_isPullback.ofInvertible` as proper pushforward of
Chow-level Gysin, after reindexing `k - 1 + 1 = k`. -/
theorem chowGysin_isPullback.ofInvertible_apply {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    chowGysin_isPullback.ofInvertible δ pX L s j i' g square k =
      (Hom.properPushforward δ
          (zeroSchemeι ((Modules.pullback g).obj L)
            (Modules.sectionsPullback g L s) ≫ g ≫ pX)
          (j ≫ zeroSchemeι L s ≫ pX)
          (gysinBaseChangeIso L s j i' g square).hom
          (gysinBaseChangeIso_hom_comp_structure pX L s j i' g square)
          (k - 1)).comp
        ((Hom.chowGysin δ (g ≫ pX) ((Modules.pullback g).obj L)
            (Modules.sectionsPullback g L s) (k - 1)).comp
          (ChowCohomology.castChowGroup δ (g ≫ pX)
            (sub_add_cancel k 1).symm)) :=
  sorry

/-- Chow-level refined Gysin along the left vertical of a cartesian square
for `zeroSchemeι L s`, transported along `gysinBaseChangeIso`. Invertibility
of the pulled-back module is supplied by `Modules.isInvertibleObject_pullback`. -/
noncomputable def chowGysin_isPullback {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    Hom.chowGroup (g ≫ pX) δ k →+
      Hom.chowGroup (j ≫ zeroSchemeι L s ≫ pX) δ (k - 1) :=
  @chowGysin_isPullback.ofInvertible _ _ _ _ _ δ _ pX _ _ L _ s _ _ j i' g _ _ _ _
    (Modules.isInvertibleObject_pullback g L) square k

/-- Cap family of transported Chow-level Gysin maps, as a degree-`1`
operation. -/
noncomputable def gysinCapFamily : CapFamily δ pX (zeroSchemeι L s) 1 :=
  fun {D' X'} (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
      [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
      [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
      [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
      (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) ↦
    chowGysin_isPullback δ pX L s j i' g square k

/-- Unfolding of `gysinCapFamily` as cartesian refined Gysin. -/
theorem gysinCapFamily_apply {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    gysinCapFamily δ pX L s j i' g square k =
      chowGysin_isPullback δ pX L s j i' g square k :=
  sorry

/-- The Gysin cap family is compatible with proper pushforward. -/
theorem gysinCapFamily_map_proper :
    CompatibleWithProperPushforward δ pX (zeroSchemeι L s)
      (gysinCapFamily δ pX L s) :=
  sorry

/-- The Gysin cap family is compatible with flat pullback. -/
theorem gysinCapFamily_pullback_flat :
    CompatibleWithFlatPullback δ pX (zeroSchemeι L s)
      (gysinCapFamily δ pX L s) :=
  sorry

/-- The Gysin cap family is compatible with Cartier Gysin. -/
theorem gysinCapFamily_gysin_cartier :
    CompatibleWithCartierGysin δ pX (zeroSchemeι L s)
      (gysinCapFamily δ pX L s) :=
  sorry

/-- Lemma 82.26.6: In Situation 82.2.1 let `X / B` be good. Let
`(L, s, i : D ⟶ X)` be a triple as in Definition 82.22.1, with
`i = zeroSchemeι L s` and `D = (zeroScheme L s).X`. Then the rule
that to `f : X' ⟶ X` assigns `(i')^* : CH_k(X') →+ CH_{k - 1}(D')`
where `D' = D ×_X X'` is a bivariant class of degree `1`. -/
@[stacks 0ERP]
noncomputable def gysin : BivariantClass δ pX (zeroSchemeι L s) 1 :=
  ofCap δ pX (zeroSchemeι L s) (gysinCapFamily δ pX L s)
    (gysinCapFamily_map_proper δ pX L s)
    (gysinCapFamily_pullback_flat δ pX L s)
    (gysinCapFamily_gysin_cartier δ pX L s)

/-- The cap maps of `gysin` are the transported Chow-level Gysin maps. -/
theorem gysin_cap {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    (gysin δ pX L s).cap j i' g square k =
      gysinCapFamily δ pX L s j i' g square k :=
  sorry

/-- On the chosen fibre product `D' = D ×_X X'`, the cap of `gysin` is the
transported Chow-level Gysin along `pullback.snd (zeroSchemeι L s) g`. -/
theorem gysin_cap_pullback {X' : AlgebraicSpace S} (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (pullback.fst (zeroSchemeι L s) g ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType
      (pullback.fst (zeroSchemeι L s) g ≫ zeroSchemeι L s ≫ pX)] (k : ℤ) :
    cap_pullback δ pX (zeroSchemeι L s) (gysin δ pX L s) g k =
      chowGysin_isPullback δ pX L s
        (pullback.fst (zeroSchemeι L s) g)
        (pullback.snd (zeroSchemeι L s) g) g
        (IsPullback.of_hasPullback (zeroSchemeι L s) g) k :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BivariantClass
