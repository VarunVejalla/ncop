import NCop.Target
import NCop.Lemmas
import NCop.BalancedTrees
import NCop.LowerBound

/-!
This is the file intended for automated mutation.

The public interface expected by `scripts/evaluate_candidate.py` is:

* `def C1 : ℝ := ...`
* `def C2 : ℝ := ...`
* `theorem lower : NCop.BreakerLowerBound C1 := ...`
* `theorem upper : NCop.MakerUpperBound C2 := ...`

Both endpoints are proved: the balanced-tree upper strategy and the
partition-matroid lower strategy. The finite lower bound has additive slack,
which is absorbed by the asymptotic epsilon quantifier.
-/

namespace Candidate

def C1 : ℝ := 2
def C2 : ℝ := 4

theorem lower : NCop.BreakerLowerBound C1 := NCop.breakerLowerBound_two

theorem upper : NCop.MakerUpperBound C2 := NCop.makerUpperBound_four

end Candidate
