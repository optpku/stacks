module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Coherent
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/- Lemma 30.9.7 (1): if `X` is a locally Noetherian scheme and `ℱ` is a coherent
`𝒪_X`-module, then the support of `ℱ` is closed. -/
@[stacks 01Y5] #check
  (AlgebraicGeometry.Scheme.Modules.isClosed_moduleSupport ℱ :
    IsClosed (RingedSpace.moduleSupport ℱ))

variable (I : X.IdealSheafData)
variable (hI : AlgebraicGeometry.Scheme.Modules.IsSchemeTheoreticSupport ℱ I)

/- Lemma 30.9.7 (2): if `I` realizes the scheme-theoretic support of a coherent module `ℱ`
on a locally Noetherian scheme, then `ℱ` is the pushforward of a coherent module on
`I.subscheme`. -/
@[stacks 01Y5] #check
  (AlgebraicGeometry.Scheme.Modules.IsSchemeTheoreticSupport.exists_coherent_module ℱ I hI :
    ∃ 𝒢 : I.subscheme.Modules,
      ∃ _ : 𝒢.IsCoherent,
        Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ))
