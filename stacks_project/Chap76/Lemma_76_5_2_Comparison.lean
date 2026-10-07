module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_9_Lift
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_13_1
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap76.Definition_76_6_5_Conormal

/-!
# Étale-chart comparison of conormal sheaves of immersions of algebraic spaces

For an immersion `i : Z ⟶ X` of algebraic spaces over a scheme `S` and an étale
morphism `φ : U ⟶ X` from a scheme, the fibre product `Z_U = U ×_X Z` is a
locally closed subscheme of `U`. Restriction of `C_{Z/X}` to `Z_U` is canonically
identified with `C_{Z_U/U}` as quasi-coherent `𝒪_{Z_U}`-modules, functorially in
the étale chart `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Module pullback of algebraic spaces is a left adjoint, hence preserves cokernels. -/
instance instIsLeftAdjoint_modulesPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (h : X ⟶ Y) : (Modules.pullback h).IsLeftAdjoint :=
  (Modules.pullbackPushforwardAdjunction h).isLeftAdjoint

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
variable {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]

/-- Equal morphisms of algebraic spaces induce isomorphic module pullbacks. -/
noncomputable def modulesPullbackCongr {Y W : AlgebraicSpace S} {f g : Y ⟶ W} (h : f = g) :
    Modules.pullback f ≅ Modules.pullback g :=
  eqToIso (congrArg Modules.pullback h)

/-- The fibre product `Z_U = U ×_X Z`, realised as `pullback i φ`. -/
noncomputable abbrev space : AlgebraicSpace S :=
  pullback i φ

/-- The projection `Z_U ⟶ U`, a locally closed immersion. -/
noncomputable abbrev ι : space i φ ⟶ ofOver U :=
  pullback.snd i φ

/-- The projection `Z_U ⟶ Z` along which `C_{Z/X}` is restricted to `Z_U`. -/
noncomputable abbrev toZ : space i φ ⟶ Z :=
  pullback.fst i φ

/-- The coborder kernel quotient `I / I²` of the coborder closed immersion of `i`. -/
noncomputable abbrev coborderQuotient : (Hom.coborder i).Modules :=
  Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
    (Hom.idealSheaf (IsImmersion.liftCoborder i))

/-- The coborder `X \ ∂Z` of `i`, pulled back along the étale chart `φ`. -/
noncomputable abbrev coborderPullback : AlgebraicSpace S :=
  pullback (IsImmersion.coborderRange i).ι φ

/-- Commutativity of the cone presenting `Z_U` over the coborder pullback square. -/
theorem liftToCoborder_w :
    (toZ i φ ≫ IsImmersion.liftCoborder i) ≫ (IsImmersion.coborderRange i).ι = ι i φ ≫ φ :=
  sorry

/-- The closed immersion `Z_U ⟶ U \ φ⁻¹(∂Z)` obtained by pulling back the coborder of `i`. -/
noncomputable def liftToCoborder : space i φ ⟶ coborderPullback i φ :=
  pullback.lift (toZ i φ ≫ IsImmersion.liftCoborder i) (ι i φ) (liftToCoborder_w i φ)

/-- `liftToCoborder` is a closed immersion, as the pullback of the coborder closed immersion. -/
instance instIsClosedImmersion_liftToCoborder : IsClosedImmersion (liftToCoborder i φ) :=
  sorry

/-- The image of the coborder of `ι` lands in the coborder of `i` after composing with `φ`. -/
theorem coborderHom_range_subset :
    Set.range (Points.map ((IsImmersion.coborderRange (ι i φ)).ι ≫ φ)) ⊆
      Set.range (Points.map (IsImmersion.coborderRange i).ι) :=
  sorry

/-- Factorization of `(coborderRange (ι)).ι ≫ φ` through the coborder open of `i`. -/
noncomputable def coborderHom :
    (IsImmersion.coborderRange (ι i φ)).X ⟶ Hom.coborder i :=
  Classical.choose
    ((IsOpenImmersion.exists_lift_iff_range_subset
        (IsImmersion.coborderRange i).ι
        ((IsImmersion.coborderRange (ι i φ)).ι ≫ φ)).mpr
      (coborderHom_range_subset i φ))

/-- `coborderHom` is the open-immersion factorization of `(coborderRange (ι)).ι ≫ φ`. -/
theorem coborderHom_spec :
    coborderHom i φ ≫ (IsImmersion.coborderRange i).ι =
      (IsImmersion.coborderRange (ι i φ)).ι ≫ φ :=
  Classical.choose_spec
    ((IsOpenImmersion.exists_lift_iff_range_subset
        (IsImmersion.coborderRange i).ι
        ((IsImmersion.coborderRange (ι i φ)).ι ≫ φ)).mpr
      (coborderHom_range_subset i φ))

/-- The coborder of `ι` maps to the pulled-back coborder of `i` by `pullback.lift`. -/
noncomputable def coborderToPullback :
    (IsImmersion.coborderRange (ι i φ)).X ⟶ coborderPullback i φ :=
  pullback.lift (coborderHom i φ) (IsImmersion.coborderRange (ι i φ)).ι (coborderHom_spec i φ)

/-- The coborder pullback square of the étale chart, as a commutative square of closed
immersions. -/
theorem coborderSq_w :
    toZ i φ ≫ IsImmersion.liftCoborder i =
      liftToCoborder i φ ≫ pullback.fst (IsImmersion.coborderRange i).ι φ :=
  sorry

/-- The coborder square `Z_U → coborderPullback` over `Z → coborder(i)`. -/
theorem coborderSq :
    CommSq (toZ i φ) (liftToCoborder i φ) (IsImmersion.liftCoborder i)
      (pullback.fst (IsImmersion.coborderRange i).ι φ) :=
  sorry

/-- The pulled-back coborder ideal of `i` vanishes after mapping to the structure sheaf of
the coborder of `ι`. -/
theorem pulledIdeal_vanishes :
    IdealSubobject.pullbackMap (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (pullback.fst (IsImmersion.coborderRange i).ι φ) ≫
        Hom.idealSheafMap (liftToCoborder i φ) =
      0 :=
  sorry

/-- The comparison `φ^{-1} I ⟶ I_U` of kernel ideals of Lemma 67.13.1 along the coborder
pullback square. -/
noncomputable def pulledIdealToIdeal :
    (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (Hom.idealSheaf (IsImmersion.liftCoborder i)) ⟶
      Hom.idealSheaf (liftToCoborder i φ) :=
  kernel.lift (Hom.idealSheafMap (liftToCoborder i φ))
      (IdealSubobject.pullbackMap (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (pullback.fst (IsImmersion.coborderRange i).ι φ))
      (pulledIdeal_vanishes i φ) ≫
    (Hom.idealSheaf_spec (liftToCoborder i φ)).inv

/-- The pulled coborder ideal-sheaf action followed by `pulledIdealToIdeal ≫ π` is zero. -/
theorem pulledIdealAction_comp_π :
    (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
          (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
            (Hom.idealSheaf (IsImmersion.liftCoborder i))) ≫
        pulledIdealToIdeal i φ ≫
          Modules.quotientByIdeal.π (Hom.idealSheafSubobject (liftToCoborder i φ))
            (Hom.idealSheaf (liftToCoborder i φ)) =
      0 :=
  sorry

/-- Restriction of `I / I²` along `U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`, as the cokernel descent of the
pulled kernel inclusion of Lemma 67.13.1. -/
noncomputable def restrictQuotient :
    (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderQuotient i) ⟶
      Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
        (Hom.idealSheaf (liftToCoborder i φ)) :=
  (PreservesCokernel.iso
        (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ))
        (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (Hom.idealSheaf (IsImmersion.liftCoborder i)))).hom ≫
    cokernel.desc
      ((Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
        (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (Hom.idealSheaf (IsImmersion.liftCoborder i))))
      (pulledIdealToIdeal i φ ≫
        Modules.quotientByIdeal.π (Hom.idealSheafSubobject (liftToCoborder i φ))
          (Hom.idealSheaf (liftToCoborder i φ)))
      (pulledIdealAction_comp_π i φ)

/-- Restriction of coborder `I / I²` along `U \ φ⁻¹(∂Z) ⟶ X \ ∂Z` is an isomorphism. -/
instance instIsIso_restrictQuotient : IsIso (restrictQuotient i φ) :=
  sorry

/-- The pulled coborder inclusion of `i` is a monomorphism, so `I_U` factors through
`φ⁻¹ I`. -/
instance instMono_pulledCoborderIdealι :
    Mono
      ((Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
        (Hom.idealSheafι (IsImmersion.liftCoborder i))) :=
  sorry

/-- The transported inclusion of `I_U` vanishes on the cokernel of the pulled coborder
ideal inclusion of `i`. -/
theorem idealToPulledIdeal_comp_π :
    (Hom.idealSheafι (liftToCoborder i φ) ≫
          Modules.structureModulePullbackInv
            (pullback.fst (IsImmersion.coborderRange i).ι φ)) ≫
        cokernel.π
          ((Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
            (Hom.idealSheafι (IsImmersion.liftCoborder i))) =
      0 :=
  sorry

/-- Reverse comparison `I_U ⟶ φ⁻¹ I` of kernel ideals of Lemma 67.13.1, as the
abelian factorization of the transported inclusion of `I_U` through the pulled
coborder kernel inclusion. -/
noncomputable def idealToPulledIdeal :
    Hom.idealSheaf (liftToCoborder i φ) ⟶
      (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (Hom.idealSheaf (IsImmersion.liftCoborder i)) :=
  CategoryTheory.Abelian.monoLift
    ((Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
      (Hom.idealSheafι (IsImmersion.liftCoborder i)))
    (Hom.idealSheafι (liftToCoborder i φ) ≫
      Modules.structureModulePullbackInv
        (pullback.fst (IsImmersion.coborderRange i).ι φ))
    (idealToPulledIdeal_comp_π i φ)

/-- The coborder-pullback ideal action of `liftToCoborder` followed by the reverse
kernel comparison and the pulled quotient projection is zero. -/
theorem restrictQuotientInv_comp_π :
    Modules.idealAction (Hom.idealSheafSubobject (liftToCoborder i φ))
          (Hom.idealSheaf (liftToCoborder i φ)) ≫
        idealToPulledIdeal i φ ≫
          (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
            (Modules.quotientByIdeal.π (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
              (Hom.idealSheaf (IsImmersion.liftCoborder i))) =
      0 :=
  sorry

/-- Reverse restriction of `I / I²` along `U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`, as the cokernel
descent of the reverse kernel inclusion of Lemma 67.13.1. -/
noncomputable def restrictQuotientInv :
    Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
        (Hom.idealSheaf (liftToCoborder i φ)) ⟶
      (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderQuotient i) :=
  cokernel.desc
    (Modules.idealAction (Hom.idealSheafSubobject (liftToCoborder i φ))
      (Hom.idealSheaf (liftToCoborder i φ)))
    (idealToPulledIdeal i φ ≫
      (Modules.pullback (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
        (Modules.quotientByIdeal.π (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (Hom.idealSheaf (IsImmersion.liftCoborder i))))
    (restrictQuotientInv_comp_π i φ)

/-- The reverse vanishing for the coborder comparison of `ι` along `coborderToPullback`. -/
theorem coborderι_pulledIdeal_vanishes :
    IdealSubobject.pullbackMap (Hom.idealSheafSubobject (liftToCoborder i φ))
          (coborderToPullback i φ) ≫
        Hom.idealSheafMap (IsImmersion.liftCoborder (ι i φ)) =
      0 :=
  sorry

/-- Kernel comparison of coborder ideals of `ι` along `coborderToPullback`. -/
noncomputable def coborderιPulledIdealToIdeal :
    (Modules.pullback (coborderToPullback i φ)).obj (Hom.idealSheaf (liftToCoborder i φ)) ⟶
      Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ)) :=
  kernel.lift (Hom.idealSheafMap (IsImmersion.liftCoborder (ι i φ)))
      (IdealSubobject.pullbackMap (Hom.idealSheafSubobject (liftToCoborder i φ))
        (coborderToPullback i φ))
      (coborderι_pulledIdeal_vanishes i φ) ≫
    (Hom.idealSheaf_spec (IsImmersion.liftCoborder (ι i φ))).inv

/-- The pulled ideal-sheaf action of `liftToCoborder` followed by the coborder-`ι`
comparison and the quotient projection is zero. -/
theorem coborderι_pulledIdealAction_comp_π :
    (Modules.pullback (coborderToPullback i φ)).map
          (Modules.idealAction (Hom.idealSheafSubobject (liftToCoborder i φ))
            (Hom.idealSheaf (liftToCoborder i φ))) ≫
        coborderιPulledIdealToIdeal i φ ≫
          Modules.quotientByIdeal.π
            (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
            (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) =
      0 :=
  sorry

/-- Quotient comparison of coborder ideals of `ι` along `coborderToPullback`. -/
noncomputable def coborderιRestrictQuotient :
    (Modules.pullback (coborderToPullback i φ)).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
          (Hom.idealSheaf (liftToCoborder i φ))) ⟶
      Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) :=
  (PreservesCokernel.iso (Modules.pullback (coborderToPullback i φ))
        (Modules.idealAction (Hom.idealSheafSubobject (liftToCoborder i φ))
          (Hom.idealSheaf (liftToCoborder i φ)))).hom ≫
    cokernel.desc
      ((Modules.pullback (coborderToPullback i φ)).map
        (Modules.idealAction (Hom.idealSheafSubobject (liftToCoborder i φ))
          (Hom.idealSheaf (liftToCoborder i φ))))
      (coborderιPulledIdealToIdeal i φ ≫
        Modules.quotientByIdeal.π
          (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))))
      (coborderι_pulledIdealAction_comp_π i φ)

/-- The coborder comparison of `ι` along `coborderToPullback` is an isomorphism. -/
instance instIsIso_coborderιRestrictQuotient : IsIso (coborderιRestrictQuotient i φ) :=
  sorry

/-- The pulled inclusion of the `liftToCoborder` kernel along `coborderToPullback` is a
monomorphism. -/
instance instMono_coborderιPulledIdealι :
    Mono
      ((Modules.pullback (coborderToPullback i φ)).map (Hom.idealSheafι (liftToCoborder i φ))) :=
  sorry

/-- The transported coborder inclusion of `ι` vanishes on the cokernel of the pulled
`liftToCoborder` kernel inclusion. -/
theorem coborderιIdealToPulledIdeal_comp_π :
    (Hom.idealSheafι (IsImmersion.liftCoborder (ι i φ)) ≫
          Modules.structureModulePullbackInv (coborderToPullback i φ)) ≫
        cokernel.π
          ((Modules.pullback (coborderToPullback i φ)).map
            (Hom.idealSheafι (liftToCoborder i φ))) =
      0 :=
  sorry

/-- Reverse comparison of coborder ideals of `ι` along `coborderToPullback`. -/
noncomputable def coborderιIdealToPulledIdeal :
    Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ)) ⟶
      (Modules.pullback (coborderToPullback i φ)).obj (Hom.idealSheaf (liftToCoborder i φ)) :=
  CategoryTheory.Abelian.monoLift
    ((Modules.pullback (coborderToPullback i φ)).map (Hom.idealSheafι (liftToCoborder i φ)))
    (Hom.idealSheafι (IsImmersion.liftCoborder (ι i φ)) ≫
      Modules.structureModulePullbackInv (coborderToPullback i φ))
    (coborderιIdealToPulledIdeal_comp_π i φ)

/-- The coborder-`ι` ideal action followed by the reverse kernel comparison and the
pulled quotient projection is zero. -/
theorem coborderιRestrictQuotientInv_comp_π :
    Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) ≫
        coborderιIdealToPulledIdeal i φ ≫
          (Modules.pullback (coborderToPullback i φ)).map
            (Modules.quotientByIdeal.π (Hom.idealSheafSubobject (liftToCoborder i φ))
              (Hom.idealSheaf (liftToCoborder i φ))) =
      0 :=
  sorry

/-- Reverse quotient comparison of coborder ideals of `ι` along `coborderToPullback`. -/
noncomputable def coborderιRestrictQuotientInv :
    Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) ⟶
      (Modules.pullback (coborderToPullback i φ)).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
          (Hom.idealSheaf (liftToCoborder i φ))) :=
  cokernel.desc
    (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
      (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))))
    (coborderιIdealToPulledIdeal i φ ≫
      (Modules.pullback (coborderToPullback i φ)).map
        (Modules.quotientByIdeal.π (Hom.idealSheafSubobject (liftToCoborder i φ))
          (Hom.idealSheaf (liftToCoborder i φ))))
    (coborderιRestrictQuotientInv_comp_π i φ)

/-- Identification of the composite `liftCoborder (ι) ≫ coborderToPullback` with
`liftToCoborder`. -/
theorem liftCoborder_ι_comp :
    IsImmersion.liftCoborder (ι i φ) ≫ coborderToPullback i φ = liftToCoborder i φ :=
  sorry

/-- Forward comparison `C_{Z/X}|_{Z_U} ⟶ C_{Z_U/U}` induced by coborder pullback of the
kernel ideal of Lemma 67.13.1. -/
noncomputable def restrictEtaleHom :
    (Modules.pullback (toZ i φ)).obj (conormalSheaf i) ⟶ conormalSheaf (ι i φ) :=
  (Modules.pullbackComp (toZ i φ) (IsImmersion.liftCoborder i)).hom.app (coborderQuotient i) ≫
    (modulesPullbackCongr
        (pullback.lift_fst (toZ i φ ≫ IsImmersion.liftCoborder i) (ι i φ)
          (liftToCoborder_w i φ)).symm).hom.app
      (coborderQuotient i) ≫
    (Modules.pullbackComp (liftToCoborder i φ)
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).inv.app (coborderQuotient i) ≫
    (Modules.pullback (liftToCoborder i φ)).map (restrictQuotient i φ) ≫
    (modulesPullbackCongr (liftCoborder_ι_comp i φ).symm).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
        (Hom.idealSheaf (liftToCoborder i φ))) ≫
    (Modules.pullbackComp (IsImmersion.liftCoborder (ι i φ))
        (coborderToPullback i φ)).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
        (Hom.idealSheaf (liftToCoborder i φ))) ≫
    (Modules.pullback (IsImmersion.liftCoborder (ι i φ))).map (coborderιRestrictQuotient i φ)

/-- Inverse comparison `C_{Z_U/U} ⟶ C_{Z/X}|_{Z_U}` induced by coborder pullback of the
kernel ideal of Lemma 67.13.1. -/
noncomputable def restrictEtaleInv :
    conormalSheaf (ι i φ) ⟶ (Modules.pullback (toZ i φ)).obj (conormalSheaf i) :=
  (Modules.pullback (IsImmersion.liftCoborder (ι i φ))).map
      (coborderιRestrictQuotientInv i φ) ≫
    (Modules.pullbackComp (IsImmersion.liftCoborder (ι i φ))
        (coborderToPullback i φ)).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
        (Hom.idealSheaf (liftToCoborder i φ))) ≫
    (modulesPullbackCongr (liftCoborder_ι_comp i φ).symm).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (liftToCoborder i φ))
        (Hom.idealSheaf (liftToCoborder i φ))) ≫
    (Modules.pullback (liftToCoborder i φ)).map (restrictQuotientInv i φ) ≫
    (Modules.pullbackComp (liftToCoborder i φ)
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).hom.app (coborderQuotient i) ≫
    (modulesPullbackCongr
        (pullback.lift_fst (toZ i φ ≫ IsImmersion.liftCoborder i) (ι i φ)
          (liftToCoborder_w i φ)).symm).inv.app (coborderQuotient i) ≫
    (Modules.pullbackComp (toZ i φ) (IsImmersion.liftCoborder i)).inv.app (coborderQuotient i)

/-- Canonical identification `C_{Z/X}|_{Z_U} ≅ C_{Z_U/U}` of quasi-coherent `𝒪_{Z_U}`-modules. -/
noncomputable def restrictEtale :
    (Modules.pullback (toZ i φ)).obj (conormalSheaf i) ≅ conormalSheaf (ι i φ) where
  hom := restrictEtaleHom i φ
  inv := restrictEtaleInv i φ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `restrictEtale` is `restrictEtaleHom`. -/
@[simp]
theorem restrictEtale_hom : (restrictEtale i φ).hom = restrictEtaleHom i φ :=
  sorry

/-- The inverse component of `restrictEtale` is `restrictEtaleInv`. -/
@[simp]
theorem restrictEtale_inv : (restrictEtale i φ).inv = restrictEtaleInv i φ :=
  sorry

/-- A locally closed subspace of a scheme, in particular `Z_U ⊂ U`, is a scheme. -/
instance instIsScheme_space : IsScheme (space i φ) :=
  sorry

/-- The morphism `Z_U ⟶ Z_V` induced by a morphism of étale charts. -/
noncomputable def spaceMap {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : space i φ ⟶ space i ψ :=
  pullback.map i φ i ψ (𝟙 Z) f (𝟙 X)
    ((Category.comp_id i).trans (Category.id_comp i).symm)
    ((Category.comp_id φ).trans hf.symm)

/-- `spaceMap` commutes with restriction to `Z`. -/
theorem spaceMap_comp_toZ {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : spaceMap i φ ψ f hf ≫ toZ i ψ = toZ i φ :=
  sorry

/-- `spaceMap` commutes with the locally closed immersions into the étale charts. -/
theorem spaceMap_comp_ι {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : spaceMap i φ ψ f hf ≫ ι i ψ = ι i φ ≫ f :=
  sorry

/-- The chart square `Z_U ⟶ Z_V` over `U ⟶ V` of locally closed immersions. -/
theorem chartSq {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) : CommSq (spaceMap i φ ψ f hf) (ι i φ) (ι i ψ) f :=
  sorry

/-- Reassociation of successive pullbacks of `C_{Z/X}` along `spaceMap` and `toZ`. -/
noncomputable def restrictEtaleToZReassoc {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Modules.pullback (spaceMap i φ ψ f hf)).obj
        ((Modules.pullback (toZ i ψ)).obj (conormalSheaf i)) ≅
      (Modules.pullback (toZ i φ)).obj (conormalSheaf i) :=
  (Modules.pullbackComp (spaceMap i φ ψ f hf) (toZ i ψ)).app (conormalSheaf i) ≪≫
    (modulesPullbackCongr (spaceMap_comp_toZ i φ ψ f hf)).app (conormalSheaf i)

/-- Pullback of modules along `spaceMap ≫ ι i ψ` identifies with pullback along
`ι i φ ≫ f`. -/
noncomputable def restrictEtaleιPullbackCongr {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Modules.pullback (spaceMap i φ ψ f hf ≫ ι i ψ) ≅ Modules.pullback (ι i φ ≫ f) :=
  modulesPullbackCongr (spaceMap_comp_ι i φ ψ f hf)

/-- The image of the coborder of `ι i φ` lands in the coborder of `ι i ψ` after
composing with the chart morphism `f`. -/
theorem chartCoborderHom_range_subset {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Set.range (Points.map ((IsImmersion.coborderRange (ι i φ)).ι ≫ f)) ⊆
      Set.range (Points.map (IsImmersion.coborderRange (ι i ψ)).ι) :=
  sorry

/-- The coborder of `ι i φ` maps to the coborder of `ι i ψ` by the open-immersion
factorization of `(coborderRange (ι i φ)).ι ≫ f`. -/
noncomputable def chartCoborderHom {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (IsImmersion.coborderRange (ι i φ)).X ⟶ Hom.coborder (ι i ψ) :=
  Classical.choose
    ((IsOpenImmersion.exists_lift_iff_range_subset
        (IsImmersion.coborderRange (ι i ψ)).ι
        ((IsImmersion.coborderRange (ι i φ)).ι ≫ f)).mpr
      (chartCoborderHom_range_subset i φ ψ f hf))

/-- `chartCoborderHom` is the open-immersion factorization of
`(coborderRange (ι i φ)).ι ≫ f`. -/
theorem chartCoborderHom_spec {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    chartCoborderHom i φ ψ f hf ≫ (IsImmersion.coborderRange (ι i ψ)).ι =
      (IsImmersion.coborderRange (ι i φ)).ι ≫ f :=
  Classical.choose_spec
    ((IsOpenImmersion.exists_lift_iff_range_subset
        (IsImmersion.coborderRange (ι i ψ)).ι
        ((IsImmersion.coborderRange (ι i φ)).ι ≫ f)).mpr
      (chartCoborderHom_range_subset i φ ψ f hf))

/-- `spaceMap` identifies the coborder closed immersions of `ι i φ` and `ι i ψ`
after composing with `chartCoborderHom`. -/
theorem chartLiftCoborder_comp {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    spaceMap i φ ψ f hf ≫ IsImmersion.liftCoborder (ι i ψ) =
      IsImmersion.liftCoborder (ι i φ) ≫ chartCoborderHom i φ ψ f hf :=
  sorry

/-- The coborder square of closed immersions associated to a morphism of étale
charts. -/
theorem chartCoborderSq {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    CommSq (spaceMap i φ ψ f hf) (IsImmersion.liftCoborder (ι i φ))
      (IsImmersion.liftCoborder (ι i ψ)) (chartCoborderHom i φ ψ f hf) :=
  sorry

/-- The pulled coborder ideal of `ι i ψ` vanishes after mapping to the structure
sheaf of the coborder of `ι i φ`. -/
theorem chartPulledIdeal_vanishes {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    IdealSubobject.pullbackMap (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
          (chartCoborderHom i φ ψ f hf) ≫
        Hom.idealSheafMap (IsImmersion.liftCoborder (ι i φ)) =
      0 :=
  sorry

/-- Kernel comparison of coborder ideals of `ι i ψ` and `ι i φ` along
`chartCoborderHom`. -/
noncomputable def chartPulledIdealToIdeal {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Modules.pullback (chartCoborderHom i φ ψ f hf)).obj
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ))) ⟶
      Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ)) :=
  kernel.lift (Hom.idealSheafMap (IsImmersion.liftCoborder (ι i φ)))
      (IdealSubobject.pullbackMap (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
        (chartCoborderHom i φ ψ f hf))
      (chartPulledIdeal_vanishes i φ ψ f hf) ≫
    (Hom.idealSheaf_spec (IsImmersion.liftCoborder (ι i φ))).inv

/-- The pulled coborder ideal-sheaf action of `ι i ψ` followed by the chart
comparison and the quotient projection is zero. -/
theorem chartPulledIdealAction_comp_π {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Modules.pullback (chartCoborderHom i φ ψ f hf)).map
          (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
            (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) ≫
        chartPulledIdealToIdeal i φ ψ f hf ≫
          Modules.quotientByIdeal.π
            (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
            (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) =
      0 :=
  sorry

/-- Restriction of coborder `I / I²` of `ι i ψ` along `chartCoborderHom`, as the
cokernel descent of the pulled kernel inclusion. -/
noncomputable def chartRestrictQuotient {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Modules.pullback (chartCoborderHom i φ ψ f hf)).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) ⟶
      Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) :=
  (PreservesCokernel.iso (Modules.pullback (chartCoborderHom i φ ψ f hf))
        (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ))))).hom ≫
    cokernel.desc
      ((Modules.pullback (chartCoborderHom i φ ψ f hf)).map
        (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))))
      (chartPulledIdealToIdeal i φ ψ f hf ≫
        Modules.quotientByIdeal.π
          (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))))
      (chartPulledIdealAction_comp_π i φ ψ f hf)

/-- Restriction of coborder `I / I²` along a morphism of étale charts is an
isomorphism. -/
instance instIsIso_chartRestrictQuotient {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    IsIso (chartRestrictQuotient i φ ψ f hf) :=
  sorry

/-- The pulled coborder inclusion of `ι i ψ` along `chartCoborderHom` is a
monomorphism. -/
instance instMono_chartPulledIdealι {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Mono
      ((Modules.pullback (chartCoborderHom i φ ψ f hf)).map
        (Hom.idealSheafι (IsImmersion.liftCoborder (ι i ψ)))) :=
  sorry

/-- The transported coborder inclusion of `ι i φ` vanishes on the cokernel of the
pulled coborder inclusion of `ι i ψ`. -/
theorem chartIdealToPulledIdeal_comp_π {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Hom.idealSheafι (IsImmersion.liftCoborder (ι i φ)) ≫
          Modules.structureModulePullbackInv (chartCoborderHom i φ ψ f hf)) ≫
        cokernel.π
          ((Modules.pullback (chartCoborderHom i φ ψ f hf)).map
            (Hom.idealSheafι (IsImmersion.liftCoborder (ι i ψ)))) =
      0 :=
  sorry

/-- Reverse comparison of coborder ideals of `ι` along `chartCoborderHom`. -/
noncomputable def chartIdealToPulledIdeal {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ)) ⟶
      (Modules.pullback (chartCoborderHom i φ ψ f hf)).obj
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ))) :=
  CategoryTheory.Abelian.monoLift
    ((Modules.pullback (chartCoborderHom i φ ψ f hf)).map
      (Hom.idealSheafι (IsImmersion.liftCoborder (ι i ψ))))
    (Hom.idealSheafι (IsImmersion.liftCoborder (ι i φ)) ≫
      Modules.structureModulePullbackInv (chartCoborderHom i φ ψ f hf))
    (chartIdealToPulledIdeal_comp_π i φ ψ f hf)

/-- The coborder-`ι i φ` ideal action followed by the reverse chart kernel comparison
and the pulled quotient projection is zero. -/
theorem chartRestrictQuotientInv_comp_π {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) ≫
        chartIdealToPulledIdeal i φ ψ f hf ≫
          (Modules.pullback (chartCoborderHom i φ ψ f hf)).map
            (Modules.quotientByIdeal.π
              (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
              (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) =
      0 :=
  sorry

/-- Reverse restriction of coborder `I / I²` of `ι` along `chartCoborderHom`. -/
noncomputable def chartRestrictQuotientInv {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))) ⟶
      (Modules.pullback (chartCoborderHom i φ ψ f hf)).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) :=
  cokernel.desc
    (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i φ)))
      (Hom.idealSheaf (IsImmersion.liftCoborder (ι i φ))))
    (chartIdealToPulledIdeal i φ ψ f hf ≫
      (Modules.pullback (chartCoborderHom i φ ψ f hf)).map
        (Modules.quotientByIdeal.π
          (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
          (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))))
    (chartRestrictQuotientInv_comp_π i φ ψ f hf)

/-- Forward transport of `C_{Z_V/V}` along `spaceMap`, by `pullbackComp`, the
`ι` reassociation `spaceMap ≫ ι i ψ = ι i φ ≫ f`, and the coborder
ideal-quotient comparison of the chart square. -/
noncomputable def restrictEtaleιReassocHom {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Modules.pullback (spaceMap i φ ψ f hf)).obj (conormalSheaf (ι i ψ)) ⟶
      conormalSheaf (ι i φ) :=
  (Modules.pullbackComp (spaceMap i φ ψ f hf) (IsImmersion.liftCoborder (ι i ψ))).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) ≫
    (modulesPullbackCongr (chartLiftCoborder_comp i φ ψ f hf)).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) ≫
    (Modules.pullbackComp (IsImmersion.liftCoborder (ι i φ))
        (chartCoborderHom i φ ψ f hf)).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) ≫
    (Modules.pullback (IsImmersion.liftCoborder (ι i φ))).map
      (chartRestrictQuotient i φ ψ f hf)

/-- Reverse transport of `C_{Z_U/U}` along `spaceMap`, by the reverse coborder
ideal-quotient comparison of the chart square. -/
noncomputable def restrictEtaleιReassocInv {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    conormalSheaf (ι i φ) ⟶
      (Modules.pullback (spaceMap i φ ψ f hf)).obj (conormalSheaf (ι i ψ)) :=
  (Modules.pullback (IsImmersion.liftCoborder (ι i φ))).map
      (chartRestrictQuotientInv i φ ψ f hf) ≫
    (Modules.pullbackComp (IsImmersion.liftCoborder (ι i φ))
        (chartCoborderHom i φ ψ f hf)).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) ≫
    (modulesPullbackCongr (chartLiftCoborder_comp i φ ψ f hf)).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ)))) ≫
    (Modules.pullbackComp (spaceMap i φ ψ f hf) (IsImmersion.liftCoborder (ι i ψ))).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder (ι i ψ)))
        (Hom.idealSheaf (IsImmersion.liftCoborder (ι i ψ))))

/-- Transport of `C_{Z_V/V}` along `spaceMap`, using `pullbackComp`,
`modulesPullbackCongr` of `spaceMap_comp_ι`, and the coborder ideal-quotient
comparison of the chart square. -/
noncomputable def restrictEtaleιReassoc {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (Modules.pullback (spaceMap i φ ψ f hf)).obj (conormalSheaf (ι i ψ)) ≅
      conormalSheaf (ι i φ) where
  hom := restrictEtaleιReassocHom i φ ψ f hf
  inv := restrictEtaleιReassocInv i φ ψ f hf
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The identification `C_{Z/X}|_{Z_U} ≅ C_{Z_U/U}` is functorial in morphisms of étale
charts: pullback of `restrictEtale i ψ` along `spaceMap` equals `restrictEtale i φ`
after the `toZ` and `ι` reassociations. -/
theorem restrictEtale_natural {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ) :
    (Modules.pullback (spaceMap i φ ψ f hf)).map (restrictEtale i ψ).hom ≫
        (restrictEtaleιReassoc i φ ψ f hf).hom =
      (restrictEtaleToZReassoc i φ ψ f hf).hom ≫ (restrictEtale i φ).hom :=
  sorry

/-- `Z_U ⟶ U` is a locally closed immersion, `Z_U` is a scheme, and `restrictEtale`
has the constructed comparison maps. -/
theorem restrictEtale_spec :
    (restrictEtale i φ).hom = restrictEtaleHom i φ ∧
      (restrictEtale i φ).inv = restrictEtaleInv i φ ∧
      IsImmersion (ι i φ) ∧ IsScheme (space i φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal
