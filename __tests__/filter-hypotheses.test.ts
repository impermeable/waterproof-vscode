import { InfoProvider } from '../src/infoview';
import { WaterproofConfigHelper, WaterproofSetting } from '../src/helpers';

/*
    This test file aims at testing the filtering lean infoview hyptoheses functionality for different visibility settings.
*/

jest.mock('vscode', () => {}, { virtual: true });
jest.mock('../src/helpers/logger', () => {})

afterEach(() => {
    jest.clearAllMocks()   
})

// Mocks the function that returns visibilityOfHypotheses setting to return the wanted value
function setMockVisibility(visibility: string) {
    jest.spyOn(WaterproofConfigHelper, 'get').mockImplementation((setting: WaterproofSetting) => {
        if (setting == WaterproofSetting.VisibilityOfHypotheses) {
            return visibility
        }
        return 'none'
    })
}

// Simplified version of a hypotheses list from an rpc response. Has two simple hypotheses with text (a, e), two "compound" hypotheses (b, c), and one ill formatted hypothesis d.
const hyps1 =
    [{ type: { tag: [{}, { text: 'P' }] }, trace: 'a'},
     { type: { tag: [{}, { append: [{ test: 'List' }, {}] }] }, trace: 'b' },
     { type: { tag: [{}, { append: [] }] }, trace: 'c' },
     { something: 'Strange format hypothesis', trace: 'd' },
     { type: { tag: [{}, { text: 'Q' }] }, trace: 'e'}]

const goal1 = { hyps: hyps1 }

const hyps2 =
    [{ type: { tag: [{}, { text: 'A' }] }, trace: 'f' },
     { type: { tag: [{}, { append: [{ text: 'Complicated' }, {}] }] }, trace: 'g' }]

const goal2 = { hyps: hyps2 }

const response = { goals: [goal1, goal2] }


describe('Testing InfoProvider.filterHypothesesList() function', () => {
    it('should not change the list of hypotheses when visibility is "all"', () => {
        setMockVisibility('all')
        const result = InfoProvider.filterHypothesesList(hyps1.slice())
        expect(result).toEqual(hyps1)
    })

    it('should remove hypotheses that have text field in .type.tag[1] (simple hypotheses) when visibility is "limited"', () => {
        setMockVisibility('limited')
        const result = InfoProvider.filterHypothesesList(hyps1.slice())
        expect(result).toHaveLength(3)
        expect(result[0].trace).toBe('b')
        expect(result[1].trace).toBe('c')
        expect(result[2].trace).toBe('d')
    })

    it('should remove all hypotheses when visibility is "none"', () => {
        setMockVisibility('none')
        const result = InfoProvider.filterHypothesesList(hyps1.slice())
        expect(result).toHaveLength(0)
    })
})


describe('Testing InfoProvider.filterHypotheses() function when rpc method is getInteractiveGoals', () => {
    const params1 = { method : 'Lean.Widget.getInteractiveGoals' }

    it('should not change the response when visibility is "all"', () => {
        setMockVisibility('all')
        const result = InfoProvider.filterHypotheses(structuredClone(response), params1)
        expect(result).toEqual(response)
    })

    it('should remove hypotheses that have text field in .type.tag[1] (simple hypotheses) from all goals when visibility is "limited"', () => {
        setMockVisibility('limited')
        const result = InfoProvider.filterHypotheses(structuredClone(response), params1)
        expect(result.goals[0].hyps).toHaveLength(3)
        expect(result.goals[1].hyps).toHaveLength(1)
        expect(result.goals[0].hyps[0].trace).toBe('b')
        expect(result.goals[0].hyps[1].trace).toBe('c')
        expect(result.goals[0].hyps[2].trace).toBe('d')
        expect(result.goals[1].hyps[0].trace).toBe('g')
    })

    it('should remove all hypotheses from all goals when visibility is "none"', () => {
        setMockVisibility('none')
        const result = InfoProvider.filterHypotheses(structuredClone(response), params1)
        expect(result.goals[0].hyps).toHaveLength(0)
        expect(result.goals[1].hyps).toHaveLength(0)
    })
})


describe('Testing InfoProvider.filterHypotheses() function when rpc method is getInteractiveTermGoal', () => {
    const params2 = { method : 'Lean.Widget.getInteractiveTermGoal' }

    it('should not change the response when visibility is "all"', () => {
        setMockVisibility('all')
        const result = InfoProvider.filterHypotheses(structuredClone(goal1), params2)
        expect(result).toEqual(goal1)
    })

    it('should remove hypotheses that have text field in .type.tag[1] (simple hypotheses) when visibility is "limited"', () => {
        setMockVisibility('limited')
        const result = InfoProvider.filterHypotheses(structuredClone(goal1), params2)
        expect(result.hyps).toHaveLength(3)
        expect(result.hyps[0].trace).toBe('b')
        expect(result.hyps[1].trace).toBe('c')
        expect(result.hyps[2].trace).toBe('d')
    })

    it('should remove all hypotheses from the goal when visibility is "none"', () => {
        setMockVisibility('none')
        const result = InfoProvider.filterHypotheses(structuredClone(goal1), params2)
      expect(result.hyps).toHaveLength(0)
    })
})
