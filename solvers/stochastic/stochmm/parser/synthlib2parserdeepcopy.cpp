#include "parser/iface.h"

namespace SynthLib2Parser {

	using namespace std;

	template <typename T>
	vector <T> DeepCopy_v(const vector <T>& v);

	void copy_ASTBase(const ASTBase *in, ASTBase *out)
	{
		out -> LineNum = in -> LineNum;
		out -> ColNum = in -> ColNum;
	}

	ArgList DeepCopy(const ArgList& s)
	{
		ArgList ans(s);
		for (size_t i = 0; i < s.size(); i++) {
			ans[i].second = DeepCopy(s[i].second);
		}
		return s;
	}

	FunDefCmd *DeepCopy(const FunDefCmd *s)
	{
		FunDefCmd *ans = new FunDefCmd();
		copy_ASTBase(s, ans);
		ans -> Symbol = s -> Symbol;
		ans -> Arguments = DeepCopy(s -> Arguments);
		ans -> Type = DeepCopy(s -> Type);
		ans -> Def = DeepCopy(s -> Def);
		return ans;
	}

	SynthFunCmd *DeepCopy(const SynthFunCmd *s)
	{
		auto *ans = new SynthFunCmd();
		copy_ASTBase(s, ans);
        ans->SynthFunName = s->SynthFunName;
        for(auto const& Arg : s->Arguments) {
            ans->Arguments.push_back(pair<string, SortExpr*>(Arg.first, DeepCopy(Arg.second)));
        }
        ans->FunType = DeepCopy(s->FunType);
        ans->GrammarRules = DeepCopy_v(s->GrammarRules);
		return ans;
	}

    ConstraintCmd* DeepCopy(const ConstraintCmd* s)
    {
        auto Retval = new ConstraintCmd();
        copy_ASTBase(s, Retval);
        Retval->TheTerm = DeepCopy(s->TheTerm);
        return Retval;
    }

	SortDefCmd *DeepCopy(const SortDefCmd *s)
	{
		SortDefCmd *ans = new SortDefCmd();
		copy_ASTBase(s, ans);
		ans -> Symbol = s -> Symbol;
		ans -> Expr = DeepCopy(s -> Expr);
		return ans;
	}

	SetOptsCmd *DeepCopy(const SetOptsCmd *s)
	{
		return new SetOptsCmd(*s);
	}

	SortExpr *DeepCopy(const SortExpr *s)
	{
		return new SortExpr(*s);
	}

    VarDeclCmd* DeepCopy(const VarDeclCmd* s)
    {
        auto Retval = new VarDeclCmd();
        copy_ASTBase(s, Retval);
        Retval->VarName = s->VarName;
        Retval->VarType = DeepCopy(s->VarType);
        return Retval;
    }

	Term *DeepCopy(const Term *s)
	{
		Term *ans = new Term();
		copy_ASTBase(s, ans);
		ans -> TType = s -> TType;
		ans -> Symbol = s -> Symbol;
		ans -> Children = DeepCopy_v(s -> Children);
		ans -> TheLiteral = DeepCopy(s -> TheLiteral);
		return ans;
	}

	GTerm *DeepCopy(const GTerm *s)
	{
		GTerm *ans = new GTerm();
		copy_ASTBase(s, ans);
		ans -> GTType = s -> GTType;
		ans -> Symbol = s -> Symbol;
		ans -> Children = DeepCopy_v(s -> Children);
		ans -> TermSort = DeepCopy(s -> TermSort);
		return ans;
	}

	NTDef *DeepCopy(const NTDef *s)
	{
		NTDef *ans = new NTDef();
		copy_ASTBase(s, ans);
		ans -> Symbol = s -> Symbol;
		ans -> Sort = DeepCopy(s -> Sort);
		ans -> Expansions = DeepCopy_v(s -> Expansions);
		return ans;
	}

	Literal *DeepCopy(const Literal *s)
	{
		return new Literal(*s);
	}

	template <typename T>
	vector <T> DeepCopy_v(const vector <T>& v) {
		vector <T> ans(v);
		for (size_t i = 0; i < v.size(); i++) {
			ans[i] = DeepCopy(v[i]);
		}
		return ans;
	}

} /* End namespace */

