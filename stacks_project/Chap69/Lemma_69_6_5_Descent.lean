module

public import stacks_project.Chap69.Lemma_69_6_5_Twist
public import stacks_project.Chap69.Lemma_69_6_5_Regular

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
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
    { obj V := characterInvariants (tensorCharacterSectionAction ρ q F V.unop) χ
      map f := characterInvariants_map χ ((tensorPushforwardConstantInteger q F).obj.map f)
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

/-- Over the torsor cover the specified map is m ↦ (χ(g)m)g; its inverse is
evaluation at 1, as in regularCharacterEquiv. Thus it descends to an isomorphism,
including for torsion coefficients, without division by the group order. -/
theorem tensorCharacterDescentHom_isIso : IsIso (tensorCharacterDescentHom ρ q χ F) :=
  sorry

/-- The torsor descent isomorphism of the specified tensor character inclusion. -/
def tensorCharacterDescentIso :
    tensorIntegerCharacter ρ q χ F ≅ tensorCharacterIsotypic ρ q χ F :=
  @asIso _ _ _ _ (tensorCharacterDescentHom ρ q χ F)
    (tensorCharacterDescentHom_isIso ρ q χ F)

/-- Forgetting the subtype proof gives precisely the original tensor inclusion. -/
theorem tensorCharacterDescentHom_val (V : (smallEtaleSite U)ᵒᵖ)
    (s : (tensorIntegerCharacter ρ q χ F).obj.obj V) :
    ((tensorCharacterDescentHom ρ q χ F).hom.app V s).1 =
      (tensorIntegerCharacter_incl ρ q χ F).hom.app V s := rfl

/-- A semi-invariant global morphism factors sectionwise through the actual
semi-invariant subsheaf by attaching its transformation-law proof. -/
def globalCharacterSection
    (s : characterInvariants (tensorPushforwardGlobalSectionsAction ρ q F) χ) :
    constantIntegerSheaf U ⟶ tensorCharacterIsotypic ρ q χ F where
  hom :=
    { app V := AddCommGrpCat.ofHom
        { toFun := fun n ↦ ⟨s.1.hom.app V n, sorry⟩
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- Descend only semi-invariant global sections. This is not a retraction on
all sections of the regular representation, which would require averaging. -/
def tensorIntegerCharacter_fromInvariants :
    characterInvariants (tensorPushforwardGlobalSectionsAction ρ q F) χ ⟶
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
    characterInvariants (globalSectionsAction ρ q F) χ ⟶
      (globalSections U).obj (tensorIntegerCharacter ρ q χ F) :=
  characterInvariants_map χ (globalSectionsProjectionFormulaHom ρ q F)
      (fun g ↦ globalSectionsProjectionFormulaHom_equivariant ρ q F g) ≫
    tensorIntegerCharacter_fromInvariants ρ q χ F

end AlgebraicGeometry.AlgebraicSpace
