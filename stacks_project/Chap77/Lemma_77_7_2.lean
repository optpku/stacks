module

public import stacks_project.Chap77.Lemma_77_7_2_FpqcTopology
public import stacks_project.Chap77.Lemma_77_7_2_Sheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢)

/- Lemma 77.7.2 (1): In Situation 77.7.1, the functor F_iso satisfies the
sheaf property for the fpqc topology. -/
@[stacks 083H] #check
  (Modules.isomorphismFunctor_isSheaf_fpqc f u :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B)
      (Modules.isomorphismFunctor f u))

section

variable (F_inj : (SchemeOver B)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_inj.obj (op T))]
variable (hF_inj : ∀ T : SchemeOver B,
  Nonempty (F_inj.obj (op T)) ↔ Mono (Modules.baseChangeMap f T.hom u))

/- Lemma 77.7.2 (2): In Situation 77.7.1, the functor F_inj satisfies the
sheaf property for the fpqc topology. -/
@[stacks 083H] #check
  (Modules.injectivityFunctor_isSheaf_fpqc f u F_inj hF_inj :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) F_inj)

end

section

variable (F_surj : (SchemeOver B)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_surj.obj (op T))]
variable (hF_surj : ∀ T : SchemeOver B,
  Nonempty (F_surj.obj (op T)) ↔ Epi (Modules.baseChangeMap f T.hom u))

/- Lemma 77.7.2 (3): In Situation 77.7.1, the functor F_surj satisfies the
sheaf property for the fpqc topology. -/
@[stacks 083H] #check
  (Modules.surjectivityFunctor_isSheaf_fpqc f u F_surj hF_surj :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) F_surj)

end

section

variable (F_zero : (SchemeOver B)ᵒᵖ ⥤ Type u)
variable [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_zero.obj (op T))]
variable (hF_zero : ∀ T : SchemeOver B,
  Nonempty (F_zero.obj (op T)) ↔ Modules.baseChangeMap f T.hom u = 0)

/- Lemma 77.7.2 (4): In Situation 77.7.1, the functor F_zero satisfies the
sheaf property for the fpqc topology. -/
@[stacks 083H] #check
  (Modules.zeroFunctor_isSheaf_fpqc f u F_zero hF_zero :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) F_zero)

end
