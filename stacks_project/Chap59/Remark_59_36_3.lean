module

public import ReasLib.CategoryTheory.Sites.Pullback.FiniteLimits
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe v

section

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasTerminal C] [HasPullbacks C]
variable [PreservesLimit (Functor.empty.{0} C) u]
variable [PreservesLimitsOfShape WalkingCospan u]

#check (CategoryTheory.Functor.isContinuous_iff_coverPreserving_of_preservesTerminal_and_pullbacks
  u J K : u.IsContinuous J K ↔ CoverPreserving J K u)

variable [u.IsContinuous J K]

/- Remark 59.36.3: identify C with the site C₂ and D with C₁. Cover preservation is
equivalent to continuity under the terminal-object and pullback hypotheses above.
The direct image f_* : Sheaf K (Type v) ⥤ Sheaf J (Type v) is restriction along u.op,
so (f_* F)(V) = F(u(V)). Its inverse image f⁻¹ : Sheaf J (Type v) ⥤ Sheaf K (Type v)
is left adjoint to f_* and preserves finite limits. Preservation of terminal objects
is essential: continuity and preservation of pullbacks alone do not suffice. -/
@[stacks 03Q2] #check
  (CategoryTheory.Functor.SheafPullback.preservesFiniteLimitsOfTerminalAndPullbacks u J K :
    PreservesFiniteLimits (u.sheafPullback (Type v) J K))

#check (CategoryTheory.Functor.sheafPushforwardContinuous u (Type v) J K :
  Sheaf K (Type v) ⥤ Sheaf J (Type v))

#check (CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso u (Type v) J K :
  u.sheafPushforwardContinuous (Type v) J K ⋙ sheafToPresheaf J (Type v) ≅
    sheafToPresheaf K (Type v) ⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op)

#check (CategoryTheory.Functor.sheafAdjunctionContinuous u (Type v) J K :
  u.sheafPullback (Type v) J K ⊣ u.sheafPushforwardContinuous (Type v) J K)

end
