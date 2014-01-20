#if !defined __ESOLVER_ESOLVER_INC_HPP
#define __ESOLVER_ESOLVER_INC_HPP

#include "../include/ESolverForwardDecls.hpp"
#include "../include/ESolver.hpp"
#include "../include/ConcreteValueBase.hpp"
#include "../include/ExpressionBase.hpp"
#include "../include/UserExpressionBase.hpp"
#include "../include/ESType.hpp"
#include "../include/ESConcreteFunctorBase.hpp"
#include "../include/OperatorFunctorBase.hpp"
#include "../include/TheoremProver.hpp"
#include "../include/ValueVector.hpp"
#include "../include/ResourceLimitManager.hpp"
#include "../include/ESolverScope.hpp"
#include "../include/ExpressionVisitorBase.hpp"
#include "../include/CEGSolver.hpp"
#include "../include/OperatorBase.hpp"
#include "../include/FuncOperatorBase.hpp"
#include "../include/SpecFuncOperator.hpp"
#include "../include/SynthFuncOperator.hpp"

namespace ESolver {

    // typedef for scopes
    typedef ESSmartPtr<ESolverScope> Scope;

} /* End namespace */

#endif /* __ESOLVER_ESOLVER_INC_HPP */

