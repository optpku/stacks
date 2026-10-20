module

public import ReasLib.RepresentationTheory.IntegerCharacter
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TorsorProjection
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

/-! # Character twists on the small étale site -/

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Opposite SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

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


variable {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]

/-- The abelian sheaf `ℤ̲(χ) = (q_* ℤ̲)^χ` on `U_étale`, as the objectwise
`χ`-equalizer of `q_* ℤ̲`. -/
noncomputable def integerCharacterAbelianSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} where
  obj :=
    { obj V := IntegerCharacter.invariants (pushforwardConstantIntegerAction ρ q (unop V)) χ
      map f :=
        IntegerCharacter.map χ ((pushforwardConstantInteger q).obj.map f)
          (fun g ↦ pushforwardConstantInteger_map_equivariant ρ q f g)
      map_id := sorry
      map_comp := sorry }
  property := sorry

/-- The sheaf of `ℤ̲_U`-modules `ℤ̲(χ)` on `U_étale`. -/
noncomputable def integerCharacterSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    SheafOfModules.{u + 1} (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U)) :=
  abelianSheaf_integerModules (integerCharacterAbelianSheaf ρ q χ)

/-- The underlying abelian sheaf of `integerCharacterSheaf` is `ℤ̲(χ)`. -/
noncomputable def integerCharacterSheaf_toSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).obj (integerCharacterSheaf ρ q χ) ≅
      integerCharacterAbelianSheaf ρ q χ :=
  abelianSheaf_integerModules_toSheafIso (integerCharacterAbelianSheaf ρ q χ)

/-- The inclusion `ℤ̲(χ) ⟶ q_* ℤ̲` of abelian sheaves. -/
noncomputable def integerCharacterSheaf_ι
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    integerCharacterAbelianSheaf ρ q χ ⟶ pushforwardConstantInteger q where
  hom :=
    { app V := IntegerCharacter.inclusion (pushforwardConstantIntegerAction ρ q (unop V)) χ
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
  (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).obj
    (tensorObj (abelianSheaf_integerModules F) (integerCharacterSheaf ρ q χ))

/-- `tensorIntegerCharacter` is the underlying abelian sheaf of the tensor product of
`ℤ̲_U`-modules. -/
theorem tensorIntegerCharacter_def
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    tensorIntegerCharacter ρ q χ F =
      (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).obj
        (tensorObj (abelianSheaf_integerModules F)
          (integerCharacterSheaf ρ q χ)) := rfl

/-- The inclusion `F ⊗_ℤ ℤ̲(χ) ⟶ F ⊗_ℤ q_* ℤ̲` induced by `ℤ̲(χ) ⟶ q_* ℤ̲`. -/
noncomputable def tensorIntegerCharacter_incl
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    tensorIntegerCharacter ρ q χ F ⟶ tensorPushforwardConstantInteger q F :=
  (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).map
    (tensorHom (𝟙 (abelianSheaf_integerModules F))
      (abelianSheaf_integerModules_map (integerCharacterSheaf_ι ρ q χ)))

/-- Inclusion of `H^0(U, F ⊗ ℤ̲(χ))` into the `χ`-invariants of `H^0(U, F ⊗ q_* ℤ̲)`. -/
noncomputable def tensorIntegerCharacter_toInvariants
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj (tensorIntegerCharacter ρ q χ F) ⟶
      IntegerCharacter.invariants (tensorPushforwardGlobalSectionsAction ρ q F) χ :=
  AddCommGrpCat.ofHom
    { toFun := fun s =>
        ⟨(globalSections U).map (tensorIntegerCharacter_incl ρ q χ F) s, sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The reverse comparison from character-twisted global sections to semi-invariant sections. -/
noncomputable def integerCharacterSheaf_globalSectionsInv
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj (tensorIntegerCharacter ρ q χ F) ⟶
      IntegerCharacter.invariants (globalSectionsAction ρ q F) χ :=
  tensorIntegerCharacter_toInvariants ρ q χ F ≫
    IntegerCharacter.map χ (globalSectionsProjectionFormulaInv ρ q F)
      (fun g ↦ globalSectionsProjectionFormulaInv_equivariant ρ q F g)


variable (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
variable (χ : G →* ℤˣ) (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1})

/-- The actual permutation action on sections of the tensor pushforward sheaf. -/
def tensorCharacterSectionAction (V : smallEtaleSite U) :
    G →* Aut ((tensorPushforwardConstantInteger q F).obj.obj (op V)) where
  toFun g :=
    { hom := (tensorPushforwardConstantIntegerSmul ρ q F g⁻¹).hom.app (op V)
      inv := (tensorPushforwardConstantIntegerSmul ρ q F g).hom.app (op V)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- Restriction commutes with the tensor pushforward action. -/
theorem tensorCharacterSectionAction_natural
    {V V' : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ V') (g : G) :
    (tensorCharacterSectionAction ρ q F V.unop g).hom ≫
        (tensorPushforwardConstantInteger q F).obj.map f =
      (tensorPushforwardConstantInteger q F).obj.map f ≫
        (tensorCharacterSectionAction ρ q F V'.unop g).hom := sorry

/-- The actual objectwise semi-invariant subsheaf of the tensor pushforward. -/
def tensorCharacterIsotypic : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} where
  obj :=
    { obj V := IntegerCharacter.invariants (tensorCharacterSectionAction ρ q F V.unop) χ
      map f := IntegerCharacter.map χ ((tensorPushforwardConstantInteger q F).obj.map f)
        (fun g ↦ tensorCharacterSectionAction_natural ρ q F f g)
      map_id := sorry
      map_comp := sorry }
  property := sorry

/-- Tensoring the character inclusion lands in the semi-invariant subsheaf. -/
def tensorCharacterDescentHom :
    tensorIntegerCharacter ρ q χ F ⟶ tensorCharacterIsotypic ρ q χ F where
  hom :=
    { app V := AddCommGrpCat.ofHom
        { toFun := fun s ↦ ⟨(tensorIntegerCharacter_incl ρ q χ F).hom.app V s, sorry⟩
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- The inverse of the tensor character inclusion, obtained by identity-coordinate
 evaluation on the torsor cover and gluing the resulting character tensors. -/
def tensorCharacterDescentInv :
    tensorCharacterIsotypic ρ q χ F ⟶ tensorIntegerCharacter ρ q χ F where
  hom :=
    { app := fun V ↦
        let localSection := fun (T : smallEtaleSite W)
            (s : (tensorCharacterIsotypic ρ q χ F).obj.obj
              (op ((etaleRestriction q).obj T))) ↦
          let V' := op ((etaleRestriction q).obj T)
          let vector : (integerCharacterAbelianSheaf ρ q χ).obj.obj V' :=
            ⟨(Finset.univ : Finset (Fin (Nat.card G))).sum (fun n ↦
              let g : G := (Finite.equivFin G).symm n
              ((χ g : ℤˣ) : ℤ) • characterBasis ρ q T g), by sorry⟩
          let coefficient := evalAtOne ρ q F T
            ((projectionFormulaIntegerInv q F).hom.app V' s.1)
          ((SheafOfModules.toSheafCompSheafToPresheafIso (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).inv.app
            (tensorObj (abelianSheaf_integerModules F)
              (integerCharacterSheaf ρ q χ))).app V'
            (tensorSection (constantIntegerRingSheaf U) V'
              ((abelianSheaf_integerModules_toSheafIso F).inv.hom.app V' coefficient)
              ((abelianSheaf_integerModules_toSheafIso
                (integerCharacterAbelianSheaf ρ q χ)).inv.hom.app V' vector))
        (tensorIntegerCharacter ρ q χ F).property.amalgamateOfArrows
          (fun c : CharacterSections.Charts q V.unop ↦
            CharacterSections.chartToBase q V.unop c)
          (CharacterSections.charts_cover q V.unop)
          (fun c ↦ AddCommGrpCat.ofHom
            { toFun := fun s ↦ localSection c.right.unop
                ((tensorCharacterIsotypic ρ q χ F).obj.map
                  (CharacterSections.chartToBase q V.unop c).op s)
              map_zero' := sorry
              map_add' := sorry })
          (by sorry)
      naturality := sorry }

/-- Tensoring with the character sheaf identifies the tensor product with its
character semi-invariant subsheaf. -/
def tensorCharacterDescentIso :
    tensorIntegerCharacter ρ q χ F ≅ tensorCharacterIsotypic ρ q χ F where
  hom := tensorCharacterDescentHom ρ q χ F
  inv := tensorCharacterDescentInv ρ q χ F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The tensor character inclusion is invertible by the explicit descent map. -/
instance tensorCharacterDescentHom_isIso : IsIso (tensorCharacterDescentHom ρ q χ F) :=
  (tensorCharacterDescentIso ρ q χ F).isIso_hom


/-- Forgetting the subtype proof gives precisely the original tensor inclusion. -/
theorem tensorCharacterDescentHom_val (V : (smallEtaleSite U)ᵒᵖ)
    (s : (tensorIntegerCharacter ρ q χ F).obj.obj V) :
    ((tensorCharacterDescentHom ρ q χ F).hom.app V s).1 =
      (tensorIntegerCharacter_incl ρ q χ F).hom.app V s := rfl

/-- A semi-invariant global morphism factors sectionwise through the actual
semi-invariant subsheaf by attaching its transformation-law proof. -/
def globalCharacterSection
    (s : IntegerCharacter.invariants (tensorPushforwardGlobalSectionsAction ρ q F) χ) :
    (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) ⟶ tensorCharacterIsotypic ρ q χ F where
  hom :=
    { app V := AddCommGrpCat.ofHom
        { toFun := fun n ↦ ⟨s.1.hom.app V n, sorry⟩
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- Descend only semi-invariant global sections. This is not a retraction on
all sections of the regular representation, which would require averaging. -/
def tensorIntegerCharacter_fromInvariants :
    IntegerCharacter.invariants (tensorPushforwardGlobalSectionsAction ρ q F) χ ⟶
      (globalSections U).obj (tensorIntegerCharacter ρ q χ F) :=
  AddCommGrpCat.ofHom
    { toFun := fun s ↦ globalCharacterSection ρ q χ F s ≫
        (tensorCharacterDescentIso ρ q χ F).inv
      map_zero' := sorry
      map_add' := sorry }

/-- Descent is inverse to the actual inclusion on semi-invariant sections. -/
theorem tensorIntegerCharacter_fromInvariants_toInvariants :
    tensorIntegerCharacter_fromInvariants ρ q χ F ≫
      tensorIntegerCharacter_toInvariants ρ q χ F = 𝟙 _ := sorry

/-- The sectionwise inverse respects the specified character tensor sheaf. -/
theorem tensorIntegerCharacter_toInvariants_fromInvariants :
    tensorIntegerCharacter_toInvariants ρ q χ F ≫
      tensorIntegerCharacter_fromInvariants ρ q χ F = 𝟙 _ := sorry

/-- The canonical forward comparison: projection formula followed by actual
torsor character descent on the semi-invariant subsheaf. -/
def integerCharacterSheaf_globalSectionsHom :
    IntegerCharacter.invariants (globalSectionsAction ρ q F) χ ⟶
      (globalSections U).obj (tensorIntegerCharacter ρ q χ F) :=
  IntegerCharacter.map χ (globalSectionsProjectionFormulaHom ρ q F)
      (fun g ↦ globalSectionsProjectionFormulaHom_equivariant ρ q F g) ≫
    tensorIntegerCharacter_fromInvariants ρ q χ F


/-- The character subsheaf of a finite free-quotient torsor is locally free of rank one. -/
@[stacks 0727, instance]
instance integerCharacterSheaf_isFiniteLocallyFreeOfRankOne :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (integerCharacterSheaf ρ q χ) :=
  sorry

/-- For every abelian coefficient sheaf, semi-invariant sections on the torsor
identify with global sections of its character twist. -/
@[stacks 0727]
noncomputable def integerCharacterSheaf_globalSections
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    IntegerCharacter.invariants (globalSectionsAction ρ q F) χ ≅
      (globalSections U).obj (tensorIntegerCharacter ρ q χ F) where
  hom := integerCharacterSheaf_globalSectionsHom ρ q χ F
  inv := integerCharacterSheaf_globalSectionsInv ρ q χ F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward global-sections comparison is the specified projection-and-descent map. -/
theorem integerCharacterSheaf_globalSections_hom
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (integerCharacterSheaf_globalSections ρ q χ F).hom =
      integerCharacterSheaf_globalSectionsHom ρ q χ F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
