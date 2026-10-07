module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_18_12_Comparison
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Definition_69_6_2_Koszul
public import stacks_project.Chap69.Lemma_69_6_3_DerivedSections
public import stacks_project.Chap69.Lemma_69_6_5_Quotient
public import stacks_project.Chap69.Lemma_69_6_5_Sections

/-!
# Character twists of the constant integer sheaf

For a free quotient morphism `q : W ⟶ U` of a finite group action and a
character `χ : G →* ℤˣ`, the sheaf `ℤ̲(χ)` on `U_étale` is the `χ`-isotypic
subsheaf of `q_* ℤ̲`, realized as a sheaf of modules over `integerRingSheaf U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Small étale sheaves of abelian groups on an algebraic space are preadditive. -/
instance smallEtaleTopology_preadditive_addCommGrpCat (X : AlgebraicSpace S) :
    Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Slice sites of the small étale topology admit weak sheafification of abelian groups. -/
instance smallEtaleTopology_over_hasWeakSheafify_addCommGrpCat
    (X : AlgebraicSpace S) (V : smallEtaleSite X) :
    HasWeakSheafify ((smallEtaleTopology X).over V) AddCommGrpCat.{u + 1} :=
  sorry

/-- Slice sites of the small étale topology satisfy `WEqualsLocallyBijective` for abelian groups. -/
instance smallEtaleTopology_over_wEqualsLocallyBijective_addCommGrpCat
    (X : AlgebraicSpace S) (V : smallEtaleSite X) :
    ((smallEtaleTopology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- The opposite of étale restriction has pointwise right Kan extensions on abelian sheaves. -/
instance etaleRestriction_op_hasPointwiseRightKanExtension_addCommGrpCat
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (F : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleRestriction f).op.HasPointwiseRightKanExtension F :=
  sorry

/-- Sheaves of modules over the constant integer ring sheaf are monoidal. -/
noncomputable instance integerRingSheaf_moduleMonoidalCategory (X : AlgebraicSpace S) :
    MonoidalCategory (SheafOfModules.{u + 1} (integerRingSheaf X)) :=
  moduleMonoidalCategory (constantIntegerRingSheaf X)

/-- The additive subgroup of `χ`-semi-invariants in an abelian group with `G`-action. -/
def characterInvariantsAddSubgroup {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    AddSubgroup A where
  carrier := { a | ∀ g : G, (σ g).hom a = ((χ g : ℤˣ) : ℤ) • a }
  zero_mem' := by
    intro g
    simp only [map_zero, zsmul_zero]
  add_mem' := by
    intro a b ha hb g
    rw [map_add, ha g, hb g, zsmul_add]
  neg_mem' := by
    intro a ha g
    rw [map_neg, ha g, zsmul_neg]

/-- The `χ`-semi-invariants of an abelian group equipped with a `G`-action. -/
noncomputable def characterInvariants {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (characterInvariantsAddSubgroup σ χ)

/-- The inclusion of `χ`-semi-invariants into the ambient abelian group. -/
noncomputable def characterInvariants_ι {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    characterInvariants σ χ ⟶ A :=
  AddCommGrpCat.ofHom (characterInvariantsAddSubgroup σ χ).subtype

/-- Membership in `characterInvariants` is the sectionwise `χ`-transformation law. -/
theorem mem_characterInvariants {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) (a : A) :
    a ∈ characterInvariantsAddSubgroup σ χ ↔
      ∀ g : G, (σ g).hom a = ((χ g : ℤˣ) : ℤ) • a := sorry

/-- A G-equivariant morphism of ambient abelian groups induces a morphism of
`χ`-semi-invariants. -/
noncomputable def characterInvariants_map {G : Type u} [Group G] [Finite G]
    {A B : AddCommGrpCat.{u + 1}} {σA : G →* Aut A} {σB : G →* Aut B}
    (χ : G →* ℤˣ) (ψ : A ⟶ B)
    (h_equivariant : ∀ g : G, (σA g).hom ≫ ψ = ψ ≫ (σB g).hom) :
    characterInvariants σA χ ⟶ characterInvariants σB χ :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ ⟨ψ (a : A), sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The `χ`-semi-invariant map intertwines the subtype inclusions. -/
theorem characterInvariants_map_ι {G : Type u} [Group G] [Finite G]
    {A B : AddCommGrpCat.{u + 1}} {σA : G →* Aut A} {σB : G →* Aut B}
    (χ : G →* ℤˣ) (ψ : A ⟶ B)
    (h_equivariant : ∀ g : G, (σA g).hom ≫ ψ = ψ ≫ (σB g).hom) :
    characterInvariants_ι σA χ ≫ ψ =
      characterInvariants_map χ ψ h_equivariant ≫ characterInvariants_ι σB χ :=
  sorry

variable {W U : AlgebraicSpace S} {G : Type u} [Group G]

/-- Equal morphisms of algebraic spaces induce isomorphic étale restriction functors. -/
noncomputable def etaleRestrictionCongrIso {X Y : AlgebraicSpace S}
    {f f' : X ⟶ Y} [Etale f] [Etale f'] (h : f = f') :
    etaleRestriction f ≅ etaleRestriction f' :=
  NatIso.ofComponents
    (fun V =>
      MorphismProperty.CostructuredArrow.isoMk (Iso.refl V.left) trivial trivial sorry)
    sorry

/-- Étale restriction is functorial in the morphism, up to a canonical isomorphism
identity on the underlying scheme. -/
noncomputable def etaleRestrictionCompIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    etaleRestriction (f ≫ g) ≅ etaleRestriction f ⋙ etaleRestriction g :=
  NatIso.ofComponents
    (fun V =>
      MorphismProperty.CostructuredArrow.isoMk (Iso.refl V.left) trivial trivial sorry)
    sorry

/-- Composite étale restriction functors are continuous. -/
instance etaleRestriction_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    (etaleRestriction f ⋙ etaleRestriction g).IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology Z) :=
  Functor.isContinuous_comp (etaleRestriction f) (etaleRestriction g)
    (smallEtaleTopology X) (smallEtaleTopology Y) (smallEtaleTopology Z)

/-- Pullback of global sections of an abelian étale sheaf along an étale morphism. -/
noncomputable def globalSectionsRestrict {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (Gsh : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (globalSections Y).obj Gsh ⟶
      (globalSections X).obj ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj Gsh) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ =>
        constantIntegerPullbackHom f ≫
          (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).map φ
      map_zero' := sorry
      map_add' := sorry }

/-- Restriction of global sections of `ℤ̲` along an étale morphism. -/
noncomputable def constantIntegerGlobalSectionsRestrict {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    (globalSections Y).obj (constantIntegerSheaf Y) ⟶
      (globalSections X).obj (constantIntegerSheaf X) :=
  globalSectionsRestrict f (constantIntegerSheaf Y) ≫
    (globalSections X).map (inv (constantIntegerPullbackHom f))

/-- An automorphism of an algebraic space acts on `Γ(X, ℤ̲)`. -/
noncomputable def constantIntegerGlobalSectionsAut {X : AlgebraicSpace S} (α : Aut X) :
    Aut ((globalSections X).obj (constantIntegerSheaf X)) where
  hom := constantIntegerGlobalSectionsRestrict α.hom
  inv := constantIntegerGlobalSectionsRestrict α.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

variable [Finite G]

/-- Identification `(ρ g)^* (F|_W) ≅ F|_W` coming from `(ρ g).hom ≫ q = q`. -/
noncomputable def restrictionPastingIso (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q] (g : G) :
    etaleRestrictionSheaf q AddCommGrpCat.{u + 1} ⋙
        etaleRestrictionSheaf (ρ g).hom AddCommGrpCat.{u + 1} ≅
      etaleRestrictionSheaf q AddCommGrpCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp (etaleRestriction (ρ g).hom)
      (etaleRestriction q) AddCommGrpCat.{u + 1} (smallEtaleTopology W)
      (smallEtaleTopology W) (smallEtaleTopology U) ≪≫
    Functor.sheafPushforwardContinuousIso (etaleRestrictionCompIso (ρ g).hom q).symm
      AddCommGrpCat.{u + 1} (smallEtaleTopology W) (smallEtaleTopology U) ≪≫
    Functor.sheafPushforwardContinuousIso
      (etaleRestrictionCongrIso (IsFreeQuotient.smul_comp g))
      AddCommGrpCat.{u + 1} (smallEtaleTopology W) (smallEtaleTopology U)

/-- The `G`-action on `H^0(W, F|_W)` by pullback along `(ρ (g⁻¹)).hom` and the
pasting identification over `U`, so that `G →* Aut` respects `Aut` multiplication. -/
noncomputable def globalSectionsAction (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    G →* Aut ((globalSections W).obj
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)) where
  toFun g :=
    { hom :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (ρ (g⁻¹)).hom ≫
                (etaleRestrictionSheaf (ρ (g⁻¹)).hom AddCommGrpCat.{u + 1}).map s ≫
                  (restrictionPastingIso ρ q (g⁻¹)).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      inv :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (ρ g).hom ≫
                (etaleRestrictionSheaf (ρ g).hom AddCommGrpCat.{u + 1}).map s ≫
                  (restrictionPastingIso ρ q g).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The identity square of a free quotient morphism is a pullback. -/
theorem isPullback_smul_comp (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (g : G) : IsPullback (ρ g).hom q q (𝟙 U) := sorry

/-- Restriction along an identity morphism is isomorphic to the identity functor
on abelian étale sheaves. -/
noncomputable def etaleRestrictionSheaf_idIso (X : AlgebraicSpace S) :
    etaleRestrictionSheaf (𝟙 X) AddCommGrpCat.{u + 1} ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (eqToIso (etaleRestriction_id X))
    AddCommGrpCat.{u + 1} (smallEtaleTopology X)

/-- Direct image `q_* ℤ̲` on `U_étale`. -/
noncomputable def pushforwardConstantInteger (q : W ⟶ U) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} :=
  (sheafPushforwardAbelian q).obj (constantIntegerSheaf W)

/-- `pushforwardConstantInteger` is abelian sheaf pushforward of `ℤ̲_W`. -/
theorem pushforwardConstantInteger_def (q : W ⟶ U) :
    pushforwardConstantInteger q =
      (sheafPushforwardAbelian q).obj (constantIntegerSheaf W) := sorry

/-- The sheaf morphism `q_* ℤ̲ ⟶ q_* ℤ̲` by base change along `(ρ g).hom`. -/
noncomputable def pushforwardConstantIntegerSmul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (g : G) :
    pushforwardConstantInteger q ⟶ pushforwardConstantInteger q :=
  (etaleRestrictionSheaf_idIso U).inv.app (pushforwardConstantInteger q) ≫
    pushforwardEtaleBaseChangeHom (isPullback_smul_comp ρ q g)
      AddCommGrpCat.{u + 1} (constantIntegerSheaf W) ≫
      (sheafPushforwardAbelian q).map (inv (constantIntegerPullbackHom (ρ g).hom))

/-- The identity of `G` acts by the identity on `q_* ℤ̲`. -/
theorem pushforwardConstantIntegerSmul_one
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] :
    pushforwardConstantIntegerSmul ρ q (1 : G) = 𝟙 _ := sorry

/-- Pullback of sections is contravariant: the raw action of a product is
first pullback by g and then pullback by h, in categorical composition order. -/
theorem pushforwardConstantIntegerSmul_mul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (g h : G) :
    pushforwardConstantIntegerSmul ρ q (g * h) =
      pushforwardConstantIntegerSmul ρ q g ≫
        pushforwardConstantIntegerSmul ρ q h := sorry

/-- The `G`-action on sections of `q_* ℤ̲` over an étale object of `U`.
The automorphism associated to `g` is pullback along `(ρ (g⁻¹)).hom`, so that
`G →* Aut` respects function-composition multiplication on `Aut`. -/
noncomputable def pushforwardConstantIntegerAction
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (V : smallEtaleSite U) :
    G →* Aut ((pushforwardConstantInteger q).obj.obj (op V)) where
  toFun g :=
    { hom := (pushforwardConstantIntegerSmul ρ q g⁻¹).hom.app (op V)
      inv := (pushforwardConstantIntegerSmul ρ q g).hom.app (op V)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- Restriction of sections of `q_* ℤ̲` is G-equivariant. -/
theorem pushforwardConstantInteger_map_equivariant
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    {V V' : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ V') (g : G) :
    ((pushforwardConstantIntegerAction ρ q (unop V)) g).hom ≫
        (pushforwardConstantInteger q).obj.map f =
      (pushforwardConstantInteger q).obj.map f ≫
        ((pushforwardConstantIntegerAction ρ q (unop V')) g).hom := sorry

/-- The abelian sheaf `ℤ̲(χ) = (q_* ℤ̲)^χ` on `U_étale`, as the objectwise
`χ`-equalizer of `q_* ℤ̲`. -/
noncomputable def integerCharacterAbelianSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} where
  obj :=
    { obj V := characterInvariants (pushforwardConstantIntegerAction ρ q (unop V)) χ
      map f :=
        characterInvariants_map χ ((pushforwardConstantInteger q).obj.map f)
          (fun g ↦ pushforwardConstantInteger_map_equivariant ρ q f g)
      map_id := sorry
      map_comp := sorry }
  property := sorry

/-- The sheaf of `ℤ̲_U`-modules `ℤ̲(χ)` on `U_étale`. -/
noncomputable def integerCharacterSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    SheafOfModules.{u + 1} (integerRingSheaf U) :=
  abelianSheaf_integerModules (integerCharacterAbelianSheaf ρ q χ)

/-- The underlying abelian sheaf of `integerCharacterSheaf` is `ℤ̲(χ)`. -/
noncomputable def integerCharacterSheaf_toSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    (SheafOfModules.toSheaf (integerRingSheaf U)).obj (integerCharacterSheaf ρ q χ) ≅
      integerCharacterAbelianSheaf ρ q χ :=
  abelianSheaf_integerModules_toSheafIso (integerCharacterAbelianSheaf ρ q χ)

/-- The inclusion `ℤ̲(χ) ⟶ q_* ℤ̲` of abelian sheaves. -/
noncomputable def integerCharacterSheaf_ι
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    integerCharacterAbelianSheaf ρ q χ ⟶ pushforwardConstantInteger q where
  hom :=
    { app V := characterInvariants_ι (pushforwardConstantIntegerAction ρ q (unop V)) χ
      naturality := sorry }

/-- Sections of `ℤ̲(χ)` are the sections of `q_* ℤ̲` that transform according to `χ`. -/
theorem integerCharacterSheaf_spec
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (V : smallEtaleSite U) (a : (pushforwardConstantInteger q).obj.obj (op V)) :
    (∃ b, (integerCharacterSheaf_ι ρ q χ).hom.app (op V) b = a) ↔
      ∀ g : G,
        ((pushforwardConstantIntegerAction ρ q V) g).hom a =
          ((χ g : ℤˣ) : ℤ) • a := sorry

/-- The abelian sheaf `F ⊗_ℤ ℤ̲(χ)` on `U_étale`. -/
noncomputable def tensorIntegerCharacter
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (integerRingSheaf U)).obj
    (tensorObj (abelianSheaf_integerModules F) (integerCharacterSheaf ρ q χ))

/-- `tensorIntegerCharacter` is the underlying abelian sheaf of the tensor product of
`ℤ̲_U`-modules. -/
theorem tensorIntegerCharacter_def
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    tensorIntegerCharacter ρ q χ F =
      (SheafOfModules.toSheaf (integerRingSheaf U)).obj
        (tensorObj (abelianSheaf_integerModules F)
          (integerCharacterSheaf ρ q χ)) := sorry

/-- Functoriality of `abelianSheaf_integerModules` on morphisms of abelian sheaves. -/
noncomputable def abelianSheaf_integerModules_map {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    abelianSheaf_integerModules F ⟶ abelianSheaf_integerModules G :=
  (PresheafOfModules.sheafification (constantIntegerRingPresheafToSheaf X)).map
    (PresheafOfModules.homMk φ.hom sorry)

/-- The abelian sheaf `F ⊗_ℤ q_* ℤ̲` on `U_étale`. -/
noncomputable def tensorPushforwardConstantInteger (q : W ⟶ U)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (integerRingSheaf U)).obj
    (tensorObj (abelianSheaf_integerModules F)
      (abelianSheaf_integerModules (pushforwardConstantInteger q)))

/-- The inclusion `F ⊗_ℤ ℤ̲(χ) ⟶ F ⊗_ℤ q_* ℤ̲` induced by `ℤ̲(χ) ⟶ q_* ℤ̲`. -/
noncomputable def tensorIntegerCharacter_incl
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    tensorIntegerCharacter ρ q χ F ⟶ tensorPushforwardConstantInteger q F :=
  (SheafOfModules.toSheaf (integerRingSheaf U)).map
    (tensorHom (𝟙 (abelianSheaf_integerModules F))
      (abelianSheaf_integerModules_map (integerCharacterSheaf_ι ρ q χ)))

/-- The `G`-action on `F ⊗_ℤ q_* ℤ̲` by acting on `q_* ℤ̲`. -/
noncomputable def tensorPushforwardConstantIntegerSmul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    tensorPushforwardConstantInteger q F ⟶ tensorPushforwardConstantInteger q F :=
  (SheafOfModules.toSheaf (integerRingSheaf U)).map
    (tensorHom (𝟙 (abelianSheaf_integerModules F))
      (abelianSheaf_integerModules_map (pushforwardConstantIntegerSmul ρ q g)))

/-- The `G`-action on `H^0(U, F ⊗_ℤ q_* ℤ̲)`. -/
noncomputable def tensorPushforwardGlobalSectionsAction
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    G →* Aut ((globalSections U).obj (tensorPushforwardConstantInteger q F)) where
  toFun g :=
    { hom := (globalSections U).map (tensorPushforwardConstantIntegerSmul ρ q F g⁻¹)
      inv := (globalSections U).map (tensorPushforwardConstantIntegerSmul ρ q F g)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The actual inverse-image comparison, adjoint to constants on all charts. -/
noncomputable def inverseImageConstantIntegerHom (q : W ⟶ U) :
    (sheafInverseImage AddCommGrpCat.{u + 1} q).obj (constantIntegerSheaf U) ⟶
      constantIntegerSheaf W :=
  CharacterSections.inverseImageConstantHom q

/-- Counit of pushforward along a free-quotient torsor: evaluate at the identity
graph of the fibre `T ×_U W`. -/
noncomputable def pushforwardCounit (q : W ⟶ U) [Etale q]
    (H : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj
        ((sheafPushforwardAbelian q).obj H) ⟶ H where
  hom :=
    { app T := AddCommGrpCat.ofHom
        { toFun := fun s ↦
            CharacterSections.pushforwardEvalIdentity q H T.unop s
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- The `G`-action on `q_* (F|_W)` by base change along `(ρ g).hom` and the
pasting identification over `U`. -/
noncomputable def restrictionPushforwardSmul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ⟶
      (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  (etaleRestrictionSheaf_idIso U).inv.app _ ≫
    pushforwardEtaleBaseChangeHom (isPullback_smul_comp ρ q g)
      AddCommGrpCat.{u + 1}
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ≫
    (sheafPushforwardAbelian q).map ((restrictionPastingIso ρ q g).hom.app F)

/-- Identity-coordinate evaluation of a pushforward section of `F|_W`. -/
noncomputable def evalAtOne
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1})
    (T : smallEtaleSite W)
    (t : ((sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj
      (op ((etaleRestriction q).obj T))) :
    F.obj.obj (op ((etaleRestriction q).obj T)) :=
  CharacterSections.pushforwardEvalIdentity q
    ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) T t

/-- The `g`-component of a torsor pushforward section is evaluation at `1` after
the inverse `G`-action. -/
noncomputable def splitComponent
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1})
    (T : smallEtaleSite W) (g : G)
    (t : ((sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj
      (op ((etaleRestriction q).obj T))) :
    F.obj.obj (op ((etaleRestriction q).obj T)) :=
  evalAtOne ρ q F T
    ((restrictionPushforwardSmul ρ q F g⁻¹).hom.app
      (op ((etaleRestriction q).obj T)) t)

/-- Cone whose value is `1` on the identity graph and `0` on every other chart. -/
noncomputable def identityBasisCone
    (q : W ⟶ U) [Etale q] (T : smallEtaleSite W) :
    Cone (StructuredArrow.proj
        (op ((etaleBaseChange q).obj ((etaleRestriction q).obj T)))
        (smallEtaleInclusion W).op ⋙ (constantIntegerSheaf W).obj) where
  pt := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  π :=
    { app := fun c ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦
            (toSheafify (smallEtaleTopology W)
                ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
              c.right
              (ULift.up (z.down * CharacterSections.identityIndicatorCoeff q T c))
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- The identity basis section `e_1` of `q_* ℤ̲` on the chart `T → U`. -/
noncomputable def identityBasis (q : W ⟶ U) [Etale q] (T : smallEtaleSite W) :
    ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)).obj.obj
      (op ((etaleRestriction q).obj T)) :=
  (((smallEtaleInclusion W).op.isPointwiseRightKanExtensionRanCounit
      (constantIntegerSheaf W).obj
      (op ((etaleBaseChange q).obj ((etaleRestriction q).obj T)))).lift
    (identityBasisCone q T)) (ULift.up 1)

/-- The regular-representation basis vector `e_g = g · e_1` of `q_* ℤ̲`. -/
noncomputable def characterBasis
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) (g : G) :
    ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)).obj.obj
      (op ((etaleRestriction q).obj T)) :=
  (pushforwardConstantIntegerSmul ρ q g).hom.app
    (op ((etaleRestriction q).obj T)) (identityBasis q T)

/-- Chartwise inverse of multiplication: `t ↦ ∑_g t_g ⊗ e_g`. -/
noncomputable def localTensor
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1})
    (T : smallEtaleSite W)
    (t : ((sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj
      (op ((etaleRestriction q).obj T))) :
    (tensorPushforwardConstantInteger q F).obj.obj
      (op ((etaleRestriction q).obj T)) :=
  let V := op ((etaleRestriction q).obj T)
  ((SheafOfModules.toSheafCompSheafToPresheafIso (integerRingSheaf U)).inv.app
    (tensorObj (abelianSheaf_integerModules F)
      (abelianSheaf_integerModules (pushforwardConstantInteger q)))).app V
    (CharacterSections.finiteSum fun g : G ↦
      tensorSection (constantIntegerRingSheaf U) V
        ((abelianSheaf_integerModules_toSheafIso F).inv.hom.app V
          (splitComponent ρ q F T g t))
        ((abelianSheaf_integerModules_toSheafIso
            (pushforwardConstantInteger q)).inv.hom.app V
          (characterBasis ρ q T g)))

/-- The forward identification `H^0(W, G) ⟶ H^0(U, q_* G)`. -/
noncomputable def globalSectionsPushforwardHom (q : W ⟶ U) [Etale q]
    (Gsh : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (globalSections W).obj Gsh ⟶
      (globalSections U).obj ((sheafPushforwardAbelian q).obj Gsh) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ =>
        (sheafInverseImageAdjunction q).homEquiv (constantIntegerSheaf U) Gsh
          (inverseImageConstantIntegerHom q ≫ φ)
      map_zero' := sorry
      map_add' := sorry }

/-- The reverse identification `H^0(U, q_* G) ⟶ H^0(W, G)`, by restricting
along `q` and evaluating at the identity graph. -/
noncomputable def globalSectionsPushforwardInv (q : W ⟶ U) [Etale q]
    (Gsh : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj ((sheafPushforwardAbelian q).obj Gsh) ⟶
      (globalSections W).obj Gsh :=
  AddCommGrpCat.ofHom
    { toFun := fun ψ =>
        constantIntegerPullbackHom q ≫
          (etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).map ψ ≫
            pushforwardCounit q Gsh
      map_zero' := sorry
      map_add' := sorry }

/-- Global sections satisfy `H^0(W, G) ≅ H^0(U, q_* G)`. -/
noncomputable def globalSectionsPushforwardIso (q : W ⟶ U) [Etale q]
    (Gsh : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (globalSections W).obj Gsh ≅
      (globalSections U).obj ((sheafPushforwardAbelian q).obj Gsh) where
  hom := globalSectionsPushforwardHom q Gsh
  inv := globalSectionsPushforwardInv q Gsh
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The constant integer sheaf, as a `ℤ̲`-module, is the monoidal unit. -/
noncomputable def abelianSheaf_integerModules_unitIso (X : AlgebraicSpace S) :
    abelianSheaf_integerModules (constantIntegerSheaf X) ≅
      SheafOfModules.unit (integerRingSheaf X) where
  hom :=
    ⟨PresheafOfModules.homMk
      ((SheafOfModules.toSheafCompSheafToPresheafIso (integerRingSheaf X)).hom.app
          (abelianSheaf_integerModules (constantIntegerSheaf X)) ≫
        (abelianSheaf_integerModules_toSheafIso (constantIntegerSheaf X)).hom.hom ≫
          (unitAbelianIso X).inv.hom ≫
            (SheafOfModules.toSheafCompSheafToPresheafIso
                (integerRingSheaf X)).inv.app
              (SheafOfModules.unit (integerRingSheaf X)))
      sorry⟩
  inv :=
    ⟨PresheafOfModules.homMk
      ((SheafOfModules.toSheafCompSheafToPresheafIso (integerRingSheaf X)).hom.app
          (SheafOfModules.unit (integerRingSheaf X)) ≫
        (unitAbelianIso X).hom.hom ≫
          (abelianSheaf_integerModules_toSheafIso (constantIntegerSheaf X)).inv.hom ≫
            (SheafOfModules.toSheafCompSheafToPresheafIso
                (integerRingSheaf X)).inv.app
              (abelianSheaf_integerModules (constantIntegerSheaf X)))
      sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical sheafification tensor-unit comparison, with no object equality. -/
noncomputable def integerModules_unitIsoTensorUnit (X : AlgebraicSpace S) :
    SheafOfModules.unit (integerRingSheaf X) ≅
      𝟙_ (SheafOfModules.{u + 1} (integerRingSheaf X)) :=
  SheafOfModules.RingedSite.unitIsoTensorUnit
    (J := smallEtaleTopology X) (𝒪 := constantIntegerRingSheaf X)

/-- The canonical projection morphism, defined on charts by multiplying the
restricted base section by the local integer coefficient. -/
noncomputable def projectionFormulaIntegerInv (q : W ⟶ U) [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    tensorPushforwardConstantInteger q F ⟶
      (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  CharacterSections.projectionHom q F

/-- On a finite torsor the chartwise projection pairing is invertible:
after the torsor cover it is the tensor comparison with a finite free module. -/
theorem projectionFormulaIntegerInv_isIso
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    IsIso (projectionFormulaIntegerInv q F) := sorry

/-- Projection formula for the actual finite torsor, inverse to the specified
chartwise multiplication map. Étaleness alone is not sufficient. -/
noncomputable def projectionFormulaInteger
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ≅
      tensorPushforwardConstantInteger q F :=
  (@asIso _ _ _ _ (projectionFormulaIntegerInv q F)
    (projectionFormulaIntegerInv_isIso ρ q F)).symm

/-- The inverse leg of the projection isomorphism is exactly chart multiplication. -/
theorem projectionFormulaInteger_inv
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (projectionFormulaInteger ρ q F).inv = projectionFormulaIntegerInv q F := rfl

/-- The forward projection comparison is the inverse of canonical chart multiplication. -/
noncomputable def projectionFormulaIntegerHom
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ⟶
      tensorPushforwardConstantInteger q F :=
  (projectionFormulaInteger ρ q F).hom

/-- The G-equivariant identification `H^0(W, F|_W) ⟶ H^0(U, F ⊗_ℤ q_* ℤ̲)`. -/
noncomputable def globalSectionsProjectionFormulaHom
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections W).obj ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ⟶
      (globalSections U).obj (tensorPushforwardConstantInteger q F) :=
  globalSectionsPushforwardHom q
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ≫
    (globalSections U).map (projectionFormulaInteger ρ q F).hom

/-- The G-equivariant identification `H^0(U, F ⊗_ℤ q_* ℤ̲) ⟶ H^0(W, F|_W)`. -/
noncomputable def globalSectionsProjectionFormulaInv
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj (tensorPushforwardConstantInteger q F) ⟶
      (globalSections W).obj ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  (globalSections U).map (projectionFormulaInteger ρ q F).inv ≫
    globalSectionsPushforwardInv q
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)

/-- Projection-formula comparison of global sections is G-equivariant. -/
theorem globalSectionsProjectionFormulaHom_equivariant
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    (globalSectionsAction ρ q F g).hom ≫
        globalSectionsProjectionFormulaHom ρ q F =
      globalSectionsProjectionFormulaHom ρ q F ≫
        (tensorPushforwardGlobalSectionsAction ρ q F g).hom := sorry

/-- Global sections of the inclusion `F ⊗ ℤ̲(χ) ⟶ F ⊗ q_* ℤ̲` are a monomorphism. -/
instance instMono_tensorIntegerCharacter_incl_globalSections
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    Mono ((globalSections U).map (tensorIntegerCharacter_incl ρ q χ F)) := sorry

/-- Reverse projection-formula comparison of global sections is G-equivariant. -/
theorem globalSectionsProjectionFormulaInv_equivariant
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    (tensorPushforwardGlobalSectionsAction ρ q F g).hom ≫
        globalSectionsProjectionFormulaInv ρ q F =
      globalSectionsProjectionFormulaInv ρ q F ≫
        (globalSectionsAction ρ q F g).hom := sorry

/-- Inclusion of `H^0(U, F ⊗ ℤ̲(χ))` into the `χ`-invariants of `H^0(U, F ⊗ q_* ℤ̲)`. -/
noncomputable def tensorIntegerCharacter_toInvariants
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj (tensorIntegerCharacter ρ q χ F) ⟶
      characterInvariants (tensorPushforwardGlobalSectionsAction ρ q F) χ :=
  AddCommGrpCat.ofHom
    { toFun := fun s =>
        ⟨(globalSections U).map (tensorIntegerCharacter_incl ρ q χ F) s, sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The reverse map of Lemma 69.6.5 (2). -/
noncomputable def integerCharacterSheaf_globalSectionsInv
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj (tensorIntegerCharacter ρ q χ F) ⟶
      characterInvariants (globalSectionsAction ρ q F) χ :=
  tensorIntegerCharacter_toInvariants ρ q χ F ≫
    characterInvariants_map χ (globalSectionsProjectionFormulaInv ρ q F)
      (fun g ↦ globalSectionsProjectionFormulaInv_equivariant ρ q F g)

end AlgebraicGeometry.AlgebraicSpace
