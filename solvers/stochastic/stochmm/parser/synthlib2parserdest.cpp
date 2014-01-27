#include "parser/iface.h"

#define RETURN_IF_NULL(__Arg) if(__Arg == NULL) return

namespace SynthLib2Parser {

    static inline void DestroyArgList(const ArgList& Args)
    {
        for(auto const& Arg : Args) {
            delete Arg.second;
        }
    }

    void DestroyFunDefCmd(FunDefCmd* Cmd)
    {
        RETURN_IF_NULL(Cmd);
        DestroySortExpr(Cmd->Type);
        DestroyArgList(Cmd->Arguments);
        DestroyTerm(Cmd->Def);
        delete Cmd;
    }

    void DestroySynthFunCmd(SynthFunCmd* Cmd)
    {
        RETURN_IF_NULL(Cmd);
        DestroyArgList(Cmd->Arguments);
        DestroySortExpr(Cmd->FunType);
        for(auto const& Rule : Cmd->GrammarRules) {
            DestroyNTDef(Rule);
        }
        delete Cmd;
    }

    void DestroyConstraintCmd(ConstraintCmd* Cmd)
    {
        RETURN_IF_NULL(Cmd);
        DestroyTerm(Cmd->TheTerm);
        delete Cmd;
    }

    void DestroyVarDeclCmd(VarDeclCmd* Cmd)
    {
        RETURN_IF_NULL(Cmd);
        DestroySortExpr(Cmd->VarType);
        delete Cmd;
    }

    void DestroySortDefCmd(SortDefCmd* Cmd)
    {
        RETURN_IF_NULL(Cmd);
        DestroySortExpr(Cmd->Expr);
        delete Cmd;
    }

    void DestroySetOptsCmd(SetOptsCmd* Cmd)
    {
        RETURN_IF_NULL(Cmd);
        delete Cmd;
    }

    void DestroySortExpr(SortExpr* Expr)
    {
        RETURN_IF_NULL(Expr);
        delete Expr;
    }

    void DestroyTerm(Term* TheTerm)
    {
        RETURN_IF_NULL(TheTerm);
        switch(TheTerm->TType) {
        case TERMTYPE_FUNC:
            for(auto const& Child : TheTerm->Children) {
                DestroyTerm(Child);
            }
            break;

        case TERMTYPE_LITERAL:
            DestroyLiteral(TheTerm->TheLiteral);

        default:
            break;
        }

        delete TheTerm;
    }

    void DestroyGTerm(GTerm* TheTerm)
    {
        RETURN_IF_NULL(TheTerm);
        switch(TheTerm->GTType) {
        case GTERMTYPE_FUNC:
            for(auto const& Child : TheTerm->Children) {
                DestroyGTerm(Child);
            }
            break;
        case GTERMTYPE_LITERAL:
            DestroyLiteral(TheTerm->TheLiteral);

        default:
            break;
        }

        DestroySortExpr(TheTerm->TermSort);
        delete TheTerm;
    }

    void DestroyNTDef(NTDef* Obj)
    {
        RETURN_IF_NULL(Obj);
        DestroySortExpr(Obj->Sort);
        for(auto const& Exp : Obj->Expansions) {
            DestroyGTerm(Exp);
        }
        delete Obj;
    }

    void DestroyLiteral(Literal* Lit)
    {
        RETURN_IF_NULL(Lit);
        delete Lit;
    }

    void DestroySetLogicCmd(SetLogicCmd* Cmd)
    {
        RETURN_IF_NULL(Cmd);
        delete Cmd;
    }

} /* End namespace */

#undef RETURN_IF_NULL

