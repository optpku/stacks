/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Big
import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Small

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

variable (S : Scheme.{u})

/- Lemma 34.3.8: the small Zariski structure on `S` is a site. -/
@[stacks 020U] #check
  (smallZariskiTopology S : GrothendieckTopology S.smallZariskiSite)

/- The big affine Zariski structure on `S` is a site. -/
#check (bigAffineZariskiTopology S : GrothendieckTopology S.bigAffineZariskiSite)

/- The small affine Zariski structure on `S` is a site. -/
#check (smallAffineZariskiTopology S : GrothendieckTopology S.smallAffineZariskiSite)

end Scheme
end AlgebraicGeometry
