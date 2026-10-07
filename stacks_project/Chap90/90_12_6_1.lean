module

public import stacks_project.Chap90.«90_12_6_1_DualNumber»
public import stacks_project.Chap90.Definition_90_12_1_TangentSpace
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Canonical map from derivations to the tangent space

For any predeformation category, the special case `V = k` of `D ↦ f_{D,*}(x_0)` is a
canonical map `γ : Derivation Λ k k → tangentSpace p`, independent of the residue-fibre
object `x_0`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

namespace CategoryTheory.Functor

/-- Predeformation categories are cofibered in groupoids, so `p.op` is fibered in groupoids. -/
instance instIsFiberedInGroupoids_op [IsPredeformationCategory p] :
    IsFibered.InGroupoids p.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- A chosen object of the residue fibre of a predeformation category, obtained from
nonemptiness of that fibre. -/
noncomputable def residueFiberPt [IsPredeformationCategory p] :
    p.Fiber (residue Λ k) :=
  Classical.choice IsPredeformationCategory.nonempty_residueFiber

/-- 90.12.6.1: for any predeformation category `p`, the special case `V = k` of
`D ↦ f_{D,*}(x_0)` is the canonical map `γ : Derivation Λ k k → tangentSpace p`,
independent of the residue-fibre object `x_0`. Here `f_D` is `derivationToDualNumber D`,
and `tangentSpace p` is the type of isomorphism classes in the fibre over `dualNumber Λ k`. -/
@[stacks 06SV]
noncomputable def tangentSpace.ofDerivation [IsPredeformationCategory p] :
    Derivation Λ k k → tangentSpace p :=
  fun D ↦
    tangentSpace.mk p
      (pushforwardFiberObj p (cleavageOp p) (derivationToDualNumber D) (residueFiberPt p))

/-- `ofDerivation p D` is the isomorphism class of the pushforward of any residue-fibre object
along `derivationToDualNumber D`, and is independent of that choice. -/
theorem tangentSpace.ofDerivation_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (D : Derivation Λ k k) :
    ofDerivation p D =
      tangentSpace.mk p (pushforwardFiberObj p (cleavageOp p) (derivationToDualNumber D) x0) :=
  sorry

end CategoryTheory.Functor
