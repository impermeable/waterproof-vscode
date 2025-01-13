We are happy to accept external contributions. If you are looking to help out, the best thing to do
is setup a [development environment](./developer-resources/developer_instructions.md) and start working on an issue.

If you don't know what to work on, but know you want to, feel free to make an issue listing your skills and interests and we can help out finding something suitable.

Below are the development guidelines of the Waterproof team. For a smooth process of contributing, it is helpful to adhere to these where you can.

Definition of ready (to work on):
- Issue is completely clear to at least two team members.
- Issue is not a draft (and therefore visible to external contributors).
- No external factors are blocking development.
- Issue has acceptation criteria. 
  - Examples:
    - Green/red bars in sidelines are shown as soon as coq-lsp finishes checking, instead of after first edit.
    - Performance issues regarding line numbers have been documented and possible easy improvements have been made. (Timebox: 4 hours for fixing easy issues.)
  - Non-examples:
    - Feature X works properly. (too vague)
    - Installing is easy. (too broad, open-ended)

Development guidelines:

- When working on an issue, make sure that: 
  - The issue is ready before starting.
  - You are assigned to the issue and the issue is "In Progress".
- When submitting a PR:
  - Review your code as if you are the reviewer.
  - Include the text `fixes #<number of issue>`. This will automatically close the issue when the PR is merged.
  - Feel free to open a *draft* pull request just to get feedback.
  - Ask someone for review using the Github interface, if you are not fully done, communicate what you want feedback on.
    - Ask for review again if you are done making changes 
- When the issue is done (according to Definition of Done below), move the issue to "Completed" on the board.

Review guidelines:

- Check out the code locally.
- Test the feature according to the test instructions and review the automated tests.
- Review the code for clarity issues, is the code easy to read?
- Check if the acceptation criteria have been fulfilled.

Definition of done:

- Code that fulfills the acceptation criteria has been merged to main branch.
- Code has been reviewed by at least one team member not involved in writing the code.
- Automated tests are included, if the feature involves the editor.
- CI build on main branch still works.
- Relevant documentation is updated.
- Corresponding issue is closed.

