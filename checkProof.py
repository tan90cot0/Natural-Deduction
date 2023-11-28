import sys

class Expression:
    def __init__(self, val, left=None, right=None):  
        self.val = val
        self.left = left
        self.right = right

def process_expression(exp):
    return exp.replace(' ', '').replace('/\\', '&').replace('\\/', '|').replace('->', '>').replace('\\bot', '~')

def process(proof_line):
    line = proof_line.split(']')
    reason = line[0][1:]
    return reason, process_expression(line[1])

def get_input(filename):
    with open(filename) as f:
        lines = f.readlines()
    for i in range(len(lines)):
        lines[i] = lines[i].strip()
    proof = lines[2:]
    statement = lines[0].split('|-')
    premises = [traverse(parse(process_expression(premise))) for premise in statement[0].split(',')]
    conclusion = statement[1]

    return proof, conclusion, premises

def parse(exp):
    if(len(exp)==0):
        return None
    if exp[0]=='(':
        curr = 0
        exp = exp[1:-1]
        for i in range(len(exp)):
            if exp[i] == '(':
                curr+= 1
            elif exp[i] == ')':
                curr-= 1
            if curr==0 and exp[i] in ['&', '|', '>', '!']:
                return Expression(exp[i], parse(exp[:i]), parse(exp[i+1:]))
    else:
        return Expression(exp)
    
def traverse(exp):
    if exp==None:
        return ''
    return traverse(exp.left) + "$" + exp.val + "$" + traverse(exp.right)

def compareTree(tree1, tree2):
    if tree1==None and tree2==None:
        return True
    if tree1==None or tree2==None:
        return False
    return tree1.val==tree2.val and compareTree(tree1.left, tree2.left) and compareTree(tree1.right, tree2.right)
    
def check_scope(indices, index, to_remove = None):
    ans = True
    for ind in indices:
        inside = False
        if to_remove in scope[ind]:
            inside = True
            scope[ind].remove(to_remove)
        ans = ans & scope[ind].issubset(scope[index])
        if inside:
            scope[ind].add(to_remove)
    return ans

def validate(reason, tree, index):
    first_space = reason.find(' ')
    if first_space!=-1:
        name, args = reason[:first_space], reason[first_space+1:].replace(' ', '').split(',')

        if name=='copy':
            ind = int(args[0])-3
            old_tree = memory[ind]
            indices = [ind]
            if check_scope(indices, index) and compareTree(old_tree, tree):
                return True
            else:
                return False
            
        elif name=='mp':
            ind1 = int(args[0])-3
            ind2 = int(args[1])-3
            a = memory[ind1]
            a_implies_b = memory[ind2]
            indices = [ind1, ind2]
            b = tree
            if check_scope(indices, index) and compareTree(a_implies_b, Expression('>', a, b)):
                return True
            else:
                return False
            
        elif name=='mt':
            ind1 = int(args[1])-3
            ind2 = int(args[0])-3
            indices = [ind1, ind2]
            not_b = memory[ind1]
            a_implies_b = memory[ind2]
            not_a = tree
            a = not_a.right
            b = not_b.right
            if check_scope(indices, index) and compareTree(a_implies_b, Expression('>', a, b)):
                return True
            else:
                return False
            
        elif name=='and-in':
            ind1 = int(args[0])-3
            ind2 = int(args[1])-3
            indices = [ind1, ind2]
            a = memory[ind1]
            b = memory[ind2]
            if check_scope(indices, index) and compareTree(tree, Expression('&', a, b)):
                return True
            else:
                return False
            
        elif name=='and-e1':
            ind = int(args[0])-3
            indices = [ind]
            a_and_b = memory[ind]
            if check_scope(indices, index) and compareTree(a_and_b.left, tree):
                return True
            else:
                return False
            
        elif name=='and-e2':
            ind = int(args[0])-3
            indices = [ind]
            a_and_b = memory[ind]
            if check_scope(indices, index) and compareTree(a_and_b.right, tree):
                return True
            else:
                return False
            
        elif name=='or-in1':
            ind = int(args[0])-3
            indices = [ind]
            a = memory[ind]
            if check_scope(indices, index) and compareTree(a, tree.left):
                return True
            else:
                return False
            
        elif name=='or-in2':
            ind = int(args[0])-3
            indices = [ind]
            a = memory[ind]
            if check_scope(indices, index) and compareTree(a, tree.right):
                return True
            else:
                return False
            
        elif name=='or-el':
            ind = int(args[0])-3
            a_or_b = memory[ind]
            
            lr = args[1].split('-')
            left1 = int(lr[0])-3
            right1 = int(lr[1])-3

            lr = args[2].split('-')
            left2 = int(lr[0])-3
            right2 = int(lr[1])-3

            if left2<=right1 and left2>=left1:
                return False
            a = memory[left1]
            b = memory[left2]
            x1 = memory[right1]
            x2 = memory[right2]
            indices1 = [left1, right1]
            indices2 = [left2, right2]
                
            if check_scope(indices1, index, assumptions[left1]) and check_scope(indices2, index, assumptions[left2]) and check_scope([ind], index) and compareTree(a_or_b, Expression('|', a, b)) and compareTree(tree, x1) and compareTree(tree, x2):
                return True
            else:
                return False

        elif name=='impl-in':
            lr = args[0].split('-')
            left = int(lr[0])-3
            right = int(lr[1])-3
            assumption = memory[left]
            implication = memory[right]
            #Check again
            indices = [left, right]

            if check_scope(indices, index, assumptions[left]) and compareTree(tree, Expression('>', assumption, implication)):
                return True
            else:
                return False
            
        elif name=='neg-in':
            lr = args[0].split('-')
            left = int(lr[0])-3
            right = int(lr[1])-3
            indices = [left, right]
            a = memory[left]
            bottom = memory[right]

            if check_scope(indices, index, assumptions[left]) and compareTree(tree.right, a) and bottom.val=='~':
                return True
            else:
                return False
            
        elif name=='neg-el':
            ind1 = int(args[0])-3
            ind2 = int(args[1])-3
            a = memory[ind1]
            not_a = memory[ind2]
            indices = [ind1, ind2]
            if check_scope(indices, index) and compareTree(a, not_a.right) and tree.val=='~':
                return True
            else:
                return False
            
        elif name=='bot-el':
            ind = int(args[0])-3
            bottom = memory[ind]
            indices = [ind]
            if check_scope(indices, index) and bottom.val=='~':
                return True
            else:
                return False
            
        elif name=='dneg-in':
            ind = int(args[0])-3
            a = memory[ind]
            not_not_a = tree
            indices = [ind]
            if check_scope(indices, index) and compareTree(a, not_not_a.right.right):
                return True
            else:
                return False
            
        elif name=='dneg-el':
            ind = int(args[0])-3
            not_not_a = memory[ind]
            indices = [ind]
            a = tree
            if check_scope(indices, index) and compareTree(a, not_not_a.right.right):
                return True
            else:
                return False
            
        elif name=='pbc':
            lr = args[0].split('-')
            left = int(lr[0])-3
            right = int(lr[1])-3
            indices = [left, right]
            not_a = memory[left]
            bottom = memory[right]
            if check_scope(indices, index, assumptions[left]) and compareTree(tree, not_a.right) and bottom.val=='~':
                return True
            else:
                return False
            
    else:
        if reason=='premise':
            if traverse(tree) in premises:
                return True
            else:
                return False
        elif reason=='assumption':
            if assumptions[index] in scope[index]:
                return True
            else:
                return False
        elif reason=='lem':
            return True

def update(assumption, left, right):
    if assumption:
        if '$' in assumption:
            ass, l, r = assumption.split('$')
            return ass+"$"+l+"$"+str(max(int(r), right))
        else:
            return assumption+"$"+str(left)+"$"+str(right)
    return assumption
        
def define_scope(reason, exp, index):
    first_space = reason.find(' ')
    if first_space!=-1:
        name, args = reason[:first_space], reason[first_space+1:].replace(' ', '').split(',')
        if name=='pbc' or name=='neg-in' or name=='impl-in':
            lr = args[0].split('-')
            left = int(lr[0])-3
            right = int(lr[1])-3
            assumptions[left] = update(assumptions[left], left, right)
            if assumptions[left]:
                for ind in range(left, right+1):
                    scope[ind].add(assumptions[left])

        elif name=='or-el':
            lr1 = args[1].split('-')
            left1 = int(lr1[0])-3
            right1 = int(lr1[1])-3

            lr2 = args[2].split('-')
            left2 = int(lr2[0])-3
            right2 = int(lr2[1])-3
            assumptions[left1] = update(assumptions[left1], left1, right1)
            assumptions[left2] = update(assumptions[left2], left2, right2)
            if assumptions[left1]:
                for ind in range(left1, right1+1):
                    scope[ind].add(assumptions[left1])
            if assumptions[left2]:
                for ind in range(left2, right2+1):
                    scope[ind].add(assumptions[left2])

    else:
        if reason=='assumption':
            assumptions[index] = exp
            pass

def checkProof(filepath):
    global conclusion, premises, memory, reasons, assumptions, scope
    proof, conclusion, premises = get_input(filepath)
    memory = [None for line in proof]
    reasons = [None for line in proof]
    assumptions = [None for line in proof]
    scope = [set() for line in proof]

    for index in range(len(proof)):
        reason, exp = process(proof[index])
        tree = parse(exp)
        reasons[index] = reason
        memory[index] = tree
        define_scope(reason, exp, index)

    if len(scope[-1])!=0 or process(proof[-1])[1] != process_expression(conclusion):
        return "incorrect"
        
    for index in range(len(proof)):
        reason, exp = process(proof[index])
        if validate(reasons[index], memory[index], index)==False:
            return "incorrect"
    return "correct"


if __name__ == '__main__':
    print(checkProof(sys.argv[1]))
